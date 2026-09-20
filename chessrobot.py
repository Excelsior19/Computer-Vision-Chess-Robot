import cv2
import numpy as np
import time
import os
import shutil
import threading
import queue
import re

try:
    import serial
    SERIAL_OK = True
except ImportError:
    SERIAL_OK = False

try:
    import chess
    import chess.engine
    CHESS_LIB_OK = True
except ImportError:
    CHESS_LIB_OK = False

# ---------- CONFIG ----------
IP_CAMERA_URL = "camera url"
BOARD_SIZE = 800
STOCKFISH_PATH = "D:\Chessrobot\stockfish-windows-x86-64-avx2.exe" # optional: full path to stockfish.exe
ENGINE_TIME_LIMIT = 0.4

PIXEL_DIFF_THRESHOLD = 26
CHANGE_SCORE_THRESHOLD = 1250
SQUARE_INNER_MARGIN = 0.20
CAPTURE_FRAMES = 6
CAPTURE_DELAY = 0.05
MIN_TOP2_RATIO = 0.42
MIN_MOVE_PAIR_SCORE = 1600
MIN_ENDPOINT_RATIO = 0.14
OCCUPIED_EMPTY_STD = 13
OCCUPIED_FILLED_STD = 16

# manual move input box (bottom-right on Board window)
MANUAL_BOX = (480, 730, 790, 790)

MANUAL_CASTLE_CODES = {
    "wsc": {"e1", "f1", "g1", "h1"},
    "wlc": {"e1", "d1", "c1", "a1"},
    "bsc": {"e8", "f8", "g8", "h8"},
    "blc": {"e8", "d8", "c8", "a8"},
}
CASTLE_KING_MOVE = {
    "wsc": ("e1", "g1"),
    "wlc": ("e1", "c1"),
    "bsc": ("e8", "g8"),
    "blc": ("e8", "c8"),
}

DIGITAL_SIZE = 480
DIGITAL_HEADER = 56
LIGHT_SQ = (210, 180, 140)
DARK_SQ = (90, 60, 30)

# ---------- ROBOT CONFIG (movementtest.py mapping) ----------
ROBOT_SERIAL_PORT = "COM3"
ROBOT_BAUD = 115200
ROBOT_Z_MIN = 60.0
ROBOT_Z_SAFE = 60.0
ROBOT_ORIGIN_X = 55.0
ROBOT_ORIGIN_Y = 19.5
ROBOT_BOARD_STEP = 24.0
ROBOT_SQUARE_X_OFFSET = -5.0
ROBOT_PHOTO_X = 234.0
ROBOT_PHOTO_Y = 225.0
ROBOT_PHOTO_Z = 60.0
ROBOT_DWELL_SEC = 2.5
SETUP_W, SETUP_H = 640, 480
STARTUP_HOME_BTN = (200, 300, 440, 360)
HOME_BTN = STARTUP_HOME_BTN  # legacy name for startup click helper

UI_STARTUP = "startup"
UI_PLACE_PIECES = "place_pieces"
UI_CHESS = "chess"

# ---------- GLOBAL ----------
points = []
selected = False
before_ref = None
overlay_indices = []
move_labels = {}
move_history = []

turn = "WHITE"
last_piece = ""
castle_text = ""
enpassant_text = ""
undo_status = ""
manual_input = ""
manual_status = ""
failed_detect = False
ep_target = None
board_perspective = None
engine_hint_frm = None
engine_hint_to = None
engine_hint_promo = None
engine_status = ""
chess_engine = None

robot_status = "Steppers disabled — click Auto Home"
robot_state = "DISABLED"
robot_ser = None
robot_lock = threading.Lock()
robot_queue = queue.Queue(maxsize=50)
robot_worker = None
robot_pos = {"X": 0.0, "Y": 0.0, "Z": 0.0}
robot_busy = False
last_robot_move = (None, None)
suppress_robot_after_undo = False

ui_phase = UI_STARTUP
cap = None
chess_ui_ready = False
feed_window_ready = False
setup_window_closed = False
camera_error = ""
feed_callbacks_bound = False
chess_callbacks_bound = False

POPUP_DURATION = 2.5
popup_text = ""
popup_until = 0.0

WHITE_BTN = (120, 340, 370, 460)
BLACK_BTN = (430, 340, 680, 460)

# ---------- PROMOTION STATE ----------
promotion_mode = False
promotion_square = None
promotion_status = ""
promotion_suggested = None
PROMO_CHOICES = ["Q", "R", "B", "N"]
PROMO_LABELS = ["Queen", "Rook", "Bishop", "Knight"]
PROMO_PANEL_Y1 = 640
PROMO_PANEL_Y2 = 760
PROMO_PANEL_X = 20
PROMO_BTN_W = 118
# ---------- BOARD MEMORY ----------
def init_board():
    board = {}
    for f in "abcdefgh":
        board[f+"2"] = "P"
        board[f+"7"] = "p"

    board.update({
        "a1":"R","h1":"R","a8":"r","h8":"r",
        "b1":"N","g1":"N","b8":"n","g8":"n",
        "c1":"B","f1":"B","c8":"b","f8":"b",
        "d1":"Q","d8":"q",
        "e1":"K","e8":"k"
    })
    return board

board_state = init_board()

# ---------- HISTORY / UNDO ----------
def save_snapshot():
    move_history.append({
        "board": board_state.copy(),
        "turn": turn,
        "last_piece": last_piece,
        "castle_text": castle_text,
        "enpassant_text": enpassant_text,
        "ep_target": ep_target,
    })

def undo_last():
    global board_state, turn, last_piece, castle_text, enpassant_text
    global before_ref, overlay_indices, move_labels, promotion_mode, promotion_square
    global undo_status, manual_status, manual_input, promotion_status, failed_detect, ep_target
    global suppress_robot_after_undo, promotion_suggested

    suppress_robot_after_undo = True
    if move_history:
        snap = move_history.pop()
        board_state = snap["board"]
        turn = snap["turn"]
        last_piece = snap["last_piece"]
        castle_text = snap["castle_text"]
        enpassant_text = snap["enpassant_text"]
        ep_target = snap.get("ep_target")
        print(f"Undone — {turn}'s turn again")
    else:
        print("Nothing to undo on board")

    before_ref = None
    overlay_indices = []
    move_labels.clear()
    promotion_mode = False
    promotion_square = None
    promotion_status = ""
    promotion_suggested = None
    undo_status = "UNDONE — R: pre-move, then R: post-move"
    manual_status = ""
    manual_input = ""
    failed_detect = False

    on_board_changed()

def undo_failed_detect():
    global before_ref, overlay_indices, move_labels, castle_text, enpassant_text
    global undo_status, manual_status, manual_input, failed_detect

    before_ref = None
    overlay_indices = []
    move_labels.clear()
    castle_text = ""
    enpassant_text = ""
    manual_status = ""
    manual_input = ""
    failed_detect = False
    undo_status = f"{turn} to move — R: pre-move, then R: post-move"
    print(f"Detection reset — still {turn}'s turn")

# ---------- HELPERS ----------
def is_white(p): return p.isupper()
def is_black(p): return p.islower()

def piece_name(p):
    return {"P":"Pawn","N":"Knight","B":"Bishop",
            "R":"Rook","Q":"Queen","K":"King"}[p.upper()]

def sq_coords(sq):
    return ord(sq[0]) - 97, int(sq[1])

def sq_str(f, r):
    return f"{chr(97 + f)}{r}"

def find_king(white, board=None):
    board = board if board is not None else board_state
    target = "K" if white else "k"
    for sq, p in board.items():
        if p == target:
            return sq
    return None

def path_clear(frm, to, board):
    f1, r1 = sq_coords(frm)
    f2, r2 = sq_coords(to)
    df, dr = f2 - f1, r2 - r1
    if df:
        df //= abs(df)
    if dr:
        dr //= abs(dr)
    f, r = f1 + df, r1 + dr
    while (f, r) != (f2, r2):
        if sq_str(f, r) in board:
            return False
        f += df
        r += dr
    return True

def piece_attacks(from_sq, to_sq, board):
    piece = board.get(from_sq)
    if not piece:
        return False
    f1, r1 = sq_coords(from_sq)
    f2, r2 = sq_coords(to_sq)
    df, dr = f2 - f1, r2 - r1
    kind = piece.upper()

    if kind == "P":
        if is_white(piece):
            return dr == 1 and abs(df) == 1
        return dr == -1 and abs(df) == 1

    if kind == "N":
        return (abs(df), abs(dr)) in [(1, 2), (2, 1)]

    if kind == "B":
        return abs(df) == abs(dr) and df != 0 and path_clear(from_sq, to_sq, board)

    if kind == "R":
        return (df == 0 or dr == 0) and (df or dr) and path_clear(from_sq, to_sq, board)

    if kind == "Q":
        return ((abs(df) == abs(dr)) or df == 0 or dr == 0) and (df or dr) and path_clear(from_sq, to_sq, board)

    if kind == "K":
        return max(abs(df), abs(dr)) == 1

    return False

def is_square_attacked(sq, by_white, board=None):
    board = board if board is not None else board_state
    for fsq, p in board.items():
        if is_white(p) == by_white and piece_attacks(fsq, sq, board):
            return True
    return False

def in_check(white, board=None):
    board = board if board is not None else board_state
    king_sq = find_king(white, board)
    if not king_sq:
        return False
    return is_square_attacked(king_sq, not white, board)

def board_after_move(frm, to, board, ep_capture=None):
    nxt = board.copy()
    nxt[to] = nxt[frm]
    del nxt[frm]
    if ep_capture and ep_capture in nxt:
        del nxt[ep_capture]
    return nxt

# ---------- MOVE VALIDATION ----------
def valid_move(piece, frm, to, capture):
    f1,r1 = frm[0],int(frm[1])
    f2,r2 = to[0],int(to[1])
    df = ord(f2)-ord(f1)
    dr = r2-r1

    if piece.upper()=="P":
        d = 1 if is_white(piece) else -1
        if capture: return abs(df)==1 and dr==d
        if df!=0: return False
        if dr==d: return True
        if (r1==2 and is_white(piece)) or (r1==7 and is_black(piece)):
            return dr==2*d
        return False

    if piece.upper()=="N": return (abs(df),abs(dr)) in [(1,2),(2,1)]
    if piece.upper()=="B": return abs(df)==abs(dr)
    if piece.upper()=="R": return df==0 or dr==0
    if piece.upper()=="Q": return abs(df)==abs(dr) or df==0 or dr==0
    if piece.upper()=="K": return max(abs(df),abs(dr))==1

    return False

def is_legal_move(frm, to, board=None, side=None):
    board = board if board is not None else board_state
    side = side or turn
    white = side == "WHITE"

    piece = board.get(frm)
    if not piece:
        return False
    if white and not is_white(piece):
        return False
    if not white and is_white(piece):
        return False

    target = board.get(to)
    if target and is_white(target) == white:
        return False

    capture = target is not None
    if not valid_move(piece, frm, to, capture):
        return False

    kind = piece.upper()
    if kind in "BRQ" and not path_clear(frm, to, board):
        return False

    if kind == "P":
        _, r1 = sq_coords(frm)
        _, r2 = sq_coords(to)
        if abs(r2 - r1) == 2:
            mid = frm[0] + str((r1 + r2) // 2)
            if mid in board:
                return False

    after = board_after_move(frm, to, board)
    return not in_check(white, after)

def is_castle_legal(squares):
    white = turn == "WHITE"
    if in_check(white):
        return False

    if squares == {"e1", "f1", "g1", "h1"} and white:
        if board_state.get("e1") != "K" or board_state.get("h1") != "R":
            return False
        if board_state.get("f1") or board_state.get("g1"):
            return False
        return not any(is_square_attacked(s, False) for s in ("e1", "f1", "g1"))

    if squares == {"e1", "d1", "c1", "a1"} and white:
        if board_state.get("e1") != "K" or board_state.get("a1") != "R":
            return False
        if board_state.get("d1") or board_state.get("c1") or board_state.get("b1"):
            return False
        return not any(is_square_attacked(s, False) for s in ("e1", "d1", "c1"))

    if squares == {"e8", "f8", "g8", "h8"} and turn == "BLACK":
        if board_state.get("e8") != "k" or board_state.get("h8") != "r":
            return False
        if board_state.get("f8") or board_state.get("g8"):
            return False
        return not any(is_square_attacked(s, True) for s in ("e8", "f8", "g8"))

    if squares == {"e8", "d8", "c8", "a8"} and turn == "BLACK":
        if board_state.get("e8") != "k" or board_state.get("a8") != "r":
            return False
        if board_state.get("d8") or board_state.get("c8") or board_state.get("b8"):
            return False
        return not any(is_square_attacked(s, True) for s in ("e8", "d8", "c8"))

    return False

# ---------- APPLY MOVE ----------
def apply_move(frm,to):
    global board_state,turn,last_piece

    piece = board_state.get(frm)

    if not piece:
        return False

    if turn=="WHITE" and not is_white(piece): return False
    if turn=="BLACK" and not is_black(piece): return False

    if not is_legal_move(frm, to):
        return False

    save_snapshot()
    board_state[to] = piece
    del board_state[frm]
    record_ep_target(frm, to, piece)

    last_piece = piece_name(piece)
    turn = "BLACK" if turn=="WHITE" else "WHITE"
    on_board_changed()
    return True

# ---------- CASTLING ----------
def detect_castle(strong):
    global board_state, turn, last_piece, castle_text, ep_target

    if len(strong) != 4:
        return None

    squares = {sq for i in strong if (sq := grid_to_chess(i))}

    if squares == {"e1","f1","g1","h1"} and turn=="WHITE" and is_castle_legal(squares):
        save_snapshot()
        board_state["g1"]="K"
        board_state["f1"]="R"
        del board_state["e1"]; del board_state["h1"]
        last_piece = "WHITE SHORT CASTLE (O-O)"
        castle_text = last_piece
        ep_target = None
        turn = "BLACK"
        on_board_changed()
        return last_piece

    if squares == {"e1","d1","c1","a1"} and turn=="WHITE" and is_castle_legal(squares):
        save_snapshot()
        board_state["c1"]="K"
        board_state["d1"]="R"
        del board_state["e1"]; del board_state["a1"]
        last_piece = "WHITE LONG CASTLE (O-O-O)"
        castle_text = last_piece
        ep_target = None
        turn = "BLACK"
        on_board_changed()
        return last_piece

    if squares == {"e8","f8","g8","h8"} and turn=="BLACK" and is_castle_legal(squares):
        save_snapshot()
        board_state["g8"]="k"
        board_state["f8"]="r"
        del board_state["e8"]; del board_state["h8"]
        last_piece = "BLACK SHORT CASTLE (O-O)"
        castle_text = last_piece
        ep_target = None
        turn = "WHITE"
        on_board_changed()
        return last_piece

    if squares == {"e8","d8","c8","a8"} and turn=="BLACK" and is_castle_legal(squares):
        save_snapshot()
        board_state["c8"]="k"
        board_state["d8"]="r"
        del board_state["e8"]; del board_state["a8"]
        last_piece = "BLACK LONG CASTLE (O-O-O)"
        castle_text = last_piece
        ep_target = None
        turn = "WHITE"
        on_board_changed()
        return last_piece

    return None

# ---------- EN PASSANT ----------
def record_ep_target(frm, to, piece):
    global ep_target
    ep_target = None
    if piece.upper() != "P":
        return
    _, r1 = sq_coords(frm)
    _, r2 = sq_coords(to)
    if is_white(piece) and r1 == 2 and r2 == 4:
        ep_target = to[0] + "3"
    elif is_black(piece) and r1 == 7 and r2 == 5:
        ep_target = to[0] + "6"

def is_en_passant_move(frm, to):
    if not ep_target or to != ep_target:
        return False
    piece = board_state.get(frm)
    if not piece or piece.upper() != "P":
        return False
    white = turn == "WHITE"
    if is_white(piece) != white:
        return False
    if abs(ord(frm[0]) - ord(to[0])) != 1:
        return False
    captured = to[0] + frm[1]
    cap = board_state.get(captured)
    if not cap or is_white(cap) == white:
        return False
    return not in_check(white, board_after_move(frm, to, board_state, ep_capture=captured))

def apply_en_passant(frm, to):
    global board_state, turn, last_piece, enpassant_text, ep_target

    if not is_en_passant_move(frm, to):
        return False

    captured = to[0] + frm[1]
    save_snapshot()
    del board_state[captured]
    board_state[to] = board_state[frm]
    del board_state[frm]
    last_piece = "En Passant"
    enpassant_text = f"{frm} -> {to} x{captured}"
    print(f"En Passant: {frm} -> {to} (captured {captured})")
    turn = "BLACK" if turn == "WHITE" else "WHITE"
    ep_target = None
    on_board_changed()
    return True

def set_ep_overlays(frm, to):
    global overlay_indices, move_labels

    captured = to[0] + frm[1]
    overlay_indices = []
    move_labels.clear()
    for sq, label in [(frm, "FROM"), (to, "TO"), (captured, "CAPT")]:
        idx = sq_to_idx(sq)
        if idx is not None:
            overlay_indices.append(idx)
            move_labels[idx] = label

def crop_inner(sq):
    h, w = sq.shape[:2]
    dx, dy = int(w * SQUARE_INNER_MARGIN), int(h * SQUARE_INNER_MARGIN)
    if dx * 2 >= w or dy * 2 >= h:
        return sq
    return sq[dy:h - dy, dx:w - dx]

def order_points(pts):
    pts = np.array(pts,dtype="float32")
    s = pts.sum(axis=1)
    d = np.diff(pts,axis=1)
    return np.array([pts[np.argmin(s)],pts[np.argmin(d)],
                     pts[np.argmax(s)],pts[np.argmax(d)]])

def warp_board(frame,pts):
    pts = order_points(pts)
    dst = np.array([[0,0],[BOARD_SIZE,0],[BOARD_SIZE,BOARD_SIZE],[0,BOARD_SIZE]],dtype="float32")
    M = cv2.getPerspectiveTransform(pts,dst)
    return cv2.warpPerspective(frame,M,(BOARD_SIZE,BOARD_SIZE))

def split_grid(board):
    step = BOARD_SIZE//8
    return [board[i*step:(i+1)*step,j*step:(j+1)*step]
            for i in range(8) for j in range(8)]

def preprocess(sq):
    inner = crop_inner(sq)
    return cv2.GaussianBlur(cv2.cvtColor(inner, cv2.COLOR_BGR2GRAY), (9, 9), 0)

def is_empty(sq):
    inner = crop_inner(sq)
    return float(np.std(cv2.cvtColor(inner, cv2.COLOR_BGR2GRAY))) < OCCUPIED_EMPTY_STD

def square_piece_present(sq_img):
    inner = crop_inner(sq_img)
    return float(np.std(cv2.cvtColor(inner, cv2.COLOR_BGR2GRAY))) >= OCCUPIED_FILLED_STD

def square_piece_present_ref(ref_patch):
    return float(np.std(ref_patch)) >= OCCUPIED_FILLED_STD

def square_empty_ref(ref_patch):
    return float(np.std(ref_patch)) < OCCUPIED_EMPTY_STD

def capture_ref(sqs):
    return [preprocess(s) for s in sqs]

def capture_ref_averaged(all_sqs):
    n = len(all_sqs)
    out = []
    for i in range(64):
        acc = None
        for sqs in all_sqs:
            p = preprocess(sqs[i]).astype(np.float32)
            acc = p if acc is None else acc + p
        out.append((acc / n).astype(np.uint8))
    return out

def compute_change(sqs, ref):
    kernel = np.ones((3, 3), np.uint8)
    out = []
    for i, s in enumerate(sqs):
        diff = cv2.absdiff(preprocess(s), ref[i])
        _, t = cv2.threshold(diff, PIXEL_DIFF_THRESHOLD, 255, cv2.THRESH_BINARY)
        t = cv2.morphologyEx(t, cv2.MORPH_OPEN, kernel)
        t = cv2.morphologyEx(t, cv2.MORPH_CLOSE, kernel)
        out.append(float(np.sum(t) / 255))
    return out

def compute_change_robust(samples, ref):
    """Blend median + peak change across frames — sensitive but stable."""
    if not samples:
        return []
    per_frame = [compute_change(sqs, ref) for sqs in samples]
    out = []
    for i in range(64):
        vals = [frame[i] for frame in per_frame]
        peak = max(vals)
        med = float(np.median(vals))
        out.append(peak * 0.5 + med * 0.5)
    return out

def is_moving_side_piece(sq):
    piece = board_state.get(sq)
    if not piece:
        return False
    if turn == "WHITE":
        return is_white(piece)
    return is_black(piece)

def is_valid_destination(sq):
    piece = board_state.get(sq)
    if piece is None:
        return True
    if turn == "WHITE":
        return is_black(piece)
    return is_white(piece)

def strong_squares(scores):
    if not scores:
        return []

    ranked = sorted(enumerate(scores), key=lambda x: -x[1])
    if ranked[0][1] <= CHANGE_SCORE_THRESHOLD:
        return []

    top = ranked[0][1]
    second = ranked[1][1] if len(ranked) > 1 else 0
    cutoff = max(CHANGE_SCORE_THRESHOLD, top * 0.36)
    picked = [i for i, s in ranked if s >= cutoff]

    if len(picked) == 1 and second >= CHANGE_SCORE_THRESHOLD * 0.85:
        if second >= top * MIN_TOP2_RATIO:
            picked.append(ranked[1][0])

    if len(picked) <= 2:
        return picked

    if len(picked) >= 3:
        third = ranked[2][1] if len(ranked) > 2 else 0
        if third < second * MIN_TOP2_RATIO:
            return picked[:2]

    return picked[:4]

def all_changed_squares(scores):
    return strong_squares(scores)

def filter_pawn_skip_squares(changed_indices, scores):
    """Drop pass-through square on two-step pawn moves (e.g. d6 when d7->d5)."""
    if len(changed_indices) < 3:
        return changed_indices

    name_to_idx = {}
    for idx in changed_indices:
        sq = grid_to_chess(idx)
        if sq:
            name_to_idx[sq] = idx

    remove_idx = set()
    for frm, fi in ((sq, name_to_idx[sq]) for sq in name_to_idx):
        piece = board_state.get(frm)
        if not piece or piece.upper() != "P" or not is_moving_side_piece(frm):
            continue
        for to in name_to_idx:
            if frm == to or not is_legal_move(frm, to):
                continue
            f1, r1 = sq_coords(frm)
            f2, r2 = sq_coords(to)
            if f1 != f2 or abs(r2 - r1) != 2:
                continue
            mid = frm[0] + str((r1 + r2) // 2)
            if mid in name_to_idx:
                remove_idx.add(name_to_idx[mid])

    return [i for i in changed_indices if i not in remove_idx]

def filter_sliding_path_squares(changed_indices, scores):
    """Drop weak intermediate squares on sliding-piece moves."""
    if len(changed_indices) < 3:
        return changed_indices

    name_to_idx = {}
    for idx in changed_indices:
        sq = grid_to_chess(idx)
        if sq:
            name_to_idx[sq] = idx

    remove_idx = set()
    for frm in name_to_idx:
        piece = board_state.get(frm)
        if not piece or piece.upper() not in "BRQ" or not is_moving_side_piece(frm):
            continue
        for to in name_to_idx:
            if frm == to or not is_legal_move(frm, to):
                continue
            f1, r1 = sq_coords(frm)
            f2, r2 = sq_coords(to)
            df, dr = f2 - f1, r2 - r1
            if df:
                df //= abs(df)
            if dr:
                dr //= abs(dr)
            fi, ti = name_to_idx[frm], name_to_idx[to]
            endpoint_score = scores[fi] + scores[ti]
            f, r = f1 + df, r1 + dr
            while (f, r) != (f2, r2):
                mid = sq_str(f, r)
                if mid in name_to_idx:
                    mi = name_to_idx[mid]
                    if scores[mi] < endpoint_score * 0.45:
                        remove_idx.add(mi)
                f += df
                r += dr

    return [i for i in changed_indices if i not in remove_idx]

def classify_occupancy_transitions(sqs, ref, scores):
    """Compare pre-move ref vs post-move image per square."""
    vacated = []
    gained = []

    for i in range(64):
        sq = grid_to_chess(i)
        if not sq:
            continue

        had = square_piece_present_ref(ref[i])
        has = square_piece_present(sqs[i])
        sc = scores[i]

        if had and not has:
            vacated.append((i, sq, sc))
        elif not had and has:
            gained.append((i, sq, sc))
        elif had and has and sc > CHANGE_SCORE_THRESHOLD * 1.15:
            gained.append((i, sq, sc))
        elif square_empty_ref(ref[i]) and has and sc > CHANGE_SCORE_THRESHOLD * 0.85:
            gained.append((i, sq, sc))
        elif had and not square_piece_present(sqs[i]) and sc > CHANGE_SCORE_THRESHOLD * 0.85:
            vacated.append((i, sq, sc))

    return vacated, gained

def endpoints_strong_enough(frm, to, scores, vacated, gained, changed_set):
    """Endpoint check — permissive for real moves, still blocks wild guesses."""
    if not is_legal_move(frm, to):
        return False

    fi, ti = chess_to_grid(frm), chess_to_grid(to)
    if fi is None or ti is None:
        return False

    combined = scores[fi] + scores[ti]
    vac_sqs = {sq for _, sq, _ in vacated}
    gain_sqs = {sq for _, sq, _ in gained}

    if frm in vac_sqs and to in gain_sqs:
        return True

    if frm in vac_sqs or to in gain_sqs:
        return combined >= MIN_MOVE_PAIR_SCORE * 0.5

    if fi in changed_set and ti in changed_set:
        if combined >= MIN_MOVE_PAIR_SCORE * 0.55:
            return True
        if (scores[fi] >= CHANGE_SCORE_THRESHOLD * 0.65 and
                scores[ti] >= CHANGE_SCORE_THRESHOLD * 0.65):
            return True

    top = max(scores) if scores else 0
    frm_ok = scores[fi] >= max(CHANGE_SCORE_THRESHOLD * 0.6, top * MIN_ENDPOINT_RATIO)
    to_ok = scores[ti] >= max(CHANGE_SCORE_THRESHOLD * 0.6, top * MIN_ENDPOINT_RATIO)
    return frm_ok and to_ok and combined >= MIN_MOVE_PAIR_SCORE * 0.65

def ep_capture_sq(frm, to):
    return to[0] + frm[1]

CASTLE_SQUARE_SETS = [
    {"e1", "f1", "g1", "h1"},
    {"e1", "d1", "c1", "a1"},
    {"e8", "f8", "g8", "h8"},
    {"e8", "d8", "c8", "a8"},
]

def try_castle_detection(scores, sqs, ref):
    """
    Detect castling by scanning all four castle squares on the board.
    Not limited to the top-N 'strong' squares (castling always changes 4 squares).
    """
    vacated, gained = classify_occupancy_transitions(sqs, ref, scores)
    occ_changed = {i for i, _, _ in vacated + gained}
    score_floor = CHANGE_SCORE_THRESHOLD * 0.38

    best = None
    for pattern in CASTLE_SQUARE_SETS:
        if not is_castle_legal(pattern):
            continue

        indices = []
        total_score = 0
        strong = 0
        for sq in pattern:
            idx = chess_to_grid(sq)
            if idx is None:
                indices = []
                break
            sc = scores[idx]
            indices.append(idx)
            total_score += sc
            if sc >= score_floor or idx in occ_changed:
                strong += 1

        if len(indices) != 4 or strong < 3:
            continue

        if best is None or total_score > best[0]:
            best = (total_score, indices)

    if not best:
        return None

    _, castle_indices = best
    msg = detect_castle(castle_indices)
    if msg:
        set_castle_overlays(castle_indices, msg)
        show_transient_popup(msg, POPUP_DURATION)
        print(msg)
        return msg
    return None

def try_castle_from_changes(changed_indices, scores):
    """Fallback: castle from already-filtered changed squares."""
    sq_map = {}
    for idx in changed_indices:
        sq = grid_to_chess(idx)
        if sq:
            sq_map[sq] = idx

    changed_set = set(sq_map)
    for pattern in CASTLE_SQUARE_SETS:
        if not pattern.issubset(changed_set):
            continue
        extras = changed_set - pattern
        if len(extras) > 1:
            continue
        if extras:
            extra_sq = next(iter(extras))
            extra_idx = sq_map[extra_sq]
            pattern_scores = [scores[sq_map[s]] for s in pattern]
            if scores[extra_idx] > max(pattern_scores) * 0.32:
                continue
        pattern_min = min(scores[sq_map[s]] for s in pattern)
        if pattern_min < CHANGE_SCORE_THRESHOLD * 0.35:
            continue
        castle_indices = [sq_map[s] for s in pattern]
        msg = detect_castle(castle_indices)
        if msg:
            set_castle_overlays(castle_indices, msg)
            show_transient_popup(msg, POPUP_DURATION)
            print(msg)
            return msg
    return None

def set_castle_overlays(indices, castle_msg=None):
    global overlay_indices, move_labels
    overlay_indices = list(indices)
    move_labels.clear()
    king_dests = {"g1", "c1", "g8", "c8"}
    for idx in indices:
        sq = grid_to_chess(idx)
        if sq in king_dests and castle_msg:
            move_labels[idx] = "O-O-O" if "O-O-O" in castle_msg else "O-O"
        else:
            move_labels[idx] = "CASTLE"

def try_en_passant_from_changes(changed_indices, scores):
    """
    En passant: from, to, and captured pawn square should appear in changes.
    """
    names = []
    for idx in changed_indices:
        sq = grid_to_chess(idx)
        if sq and sq not in names:
            names.append(sq)

    if len(names) < 2:
        return False

    best = None
    for frm in names:
        if not is_moving_side_piece(frm):
            continue
        for to in names:
            if frm == to or not is_en_passant_move(frm, to):
                continue
            cap = ep_capture_sq(frm, to)
            cap_idx = chess_to_grid(cap)
            fi, ti = chess_to_grid(frm), chess_to_grid(to)
            score = 0
            if fi is not None and ti is not None:
                score = scores[fi] + scores[ti]
            if cap in names:
                score += scores[cap_idx] if cap_idx is not None else 0
            elif cap_idx is not None and cap_idx in changed_indices:
                score += scores[cap_idx]
            else:
                continue
            if cap_idx is not None and scores[cap_idx] < CHANGE_SCORE_THRESHOLD * 0.25:
                continue
            if fi is not None and ti is not None:
                if scores[fi] + scores[ti] < MIN_MOVE_PAIR_SCORE * 0.5:
                    continue
            if best is None or score > best[0]:
                best = (score, frm, to)

    if best and apply_en_passant(best[1], best[2]):
        set_ep_overlays(best[1], best[2])
        print(f"En Passant: {best[1]} -> {best[2]} (captured {ep_capture_sq(best[1], best[2])})")
        return True
    return False

def collect_move_candidates(changed_indices, scores, sqs, ref):
    """Build scored legal move candidates from changed + occupancy data."""
    changed_indices = filter_pawn_skip_squares(changed_indices, scores)
    changed_set = set(changed_indices)

    names = []
    for idx in changed_indices:
        sq = grid_to_chess(idx)
        if sq and sq not in names:
            names.append(sq)

    vacated, gained = classify_occupancy_transitions(sqs, ref, scores)
    vac_names = [sq for _, sq, _ in vacated]
    gain_names = [sq for _, sq, _ in gained]

    candidates = []

    def add(frm, to, score, kind="normal"):
        if frm == to:
            return
        if kind == "ep":
            if is_en_passant_move(frm, to):
                candidates.append((score + 40000, frm, to, "ep"))
        elif is_legal_move(frm, to):
            candidates.append((score + 10000, frm, to, "normal"))

    for frm in vac_names:
        if not is_moving_side_piece(frm):
            continue
        for to in gain_names:
            fi, ti = chess_to_grid(frm), chess_to_grid(to)
            sc = (scores[fi] + scores[ti]) if fi is not None and ti is not None else 0
            add(frm, to, sc + 20000)

    for frm in names:
        if not is_moving_side_piece(frm):
            continue
        for to in names:
            if frm == to:
                continue
            fi, ti = chess_to_grid(frm), chess_to_grid(to)
            sc = (scores[fi] + scores[ti]) if fi is not None and ti is not None else 0
            add(frm, to, sc + 5000)

    if ep_target:
        for frm in names:
            if not is_moving_side_piece(frm):
                continue
            if is_en_passant_move(frm, ep_target):
                cap = ep_capture_sq(frm, ep_target)
                cap_idx = chess_to_grid(cap)
                if cap in names or (cap_idx is not None and cap_idx in changed_set):
                    fi = chess_to_grid(frm)
                    ti = chess_to_grid(ep_target)
                    sc = 0
                    if fi is not None:
                        sc += scores[fi]
                    if ti is not None:
                        sc += scores[ti]
                    if cap_idx is not None:
                        sc += scores[cap_idx]
                    add(frm, ep_target, sc + 35000, kind="ep")

    for frm in vac_names:
        if not is_moving_side_piece(frm):
            continue
        for to in names:
            fi, ti = chess_to_grid(frm), chess_to_grid(to)
            sc = (scores[fi] + scores[ti]) if fi is not None and ti is not None else 0
            add(frm, to, sc + 15000)

    for frm in names:
        if not is_moving_side_piece(frm):
            continue
        for to in gain_names:
            fi, ti = chess_to_grid(frm), chess_to_grid(to)
            sc = (scores[fi] + scores[ti]) if fi is not None and ti is not None else 0
            add(frm, to, sc + 15000)

    if not candidates:
        return None, None, None

    deduped = {}
    for c in candidates:
        key = (c[1], c[2])
        if key not in deduped or c[0] > deduped[key][0]:
            deduped[key] = c
    candidates = list(deduped.values())
    candidates.sort(key=lambda x: -x[0])

    verified = []
    for c in candidates:
        if endpoints_strong_enough(c[1], c[2], scores, vacated, gained, changed_set):
            verified.append(c)

    pick_from = verified if verified else candidates
    if not pick_from:
        return None, None, None

    top = pick_from[0]
    if len(pick_from) > 1 and verified:
        for alt in pick_from[1:]:
            if alt[0] < top[0] * 0.85:
                break
            if (alt[1], alt[2]) == (top[1], top[2]):
                continue
            _, r1 = sq_coords(top[1])
            _, r2 = sq_coords(top[2])
            _, ar2 = sq_coords(alt[2])
            if top[1] == alt[1] and abs(r2 - r1) == 2 and abs(ar2 - r1) == 1:
                continue
            if alt[0] >= top[0] * 0.95:
                return None, None, None

    return top[1], top[2], changed_indices

def fallback_two_square_detect(changed_indices, scores, sqs, ref):
    """Last resort: pair the two strongest changed squares if legal."""
    if len(changed_indices) < 2:
        return None, None

    ranked = sorted(changed_indices, key=lambda i: -scores[i])[:2]
    if len(ranked) < 2:
        return None, None

    g1, g2 = ranked
    sq1, sq2 = grid_to_chess(g1), grid_to_chess(g2)
    if not sq1 or not sq2:
        return None, None

    vacated, gained = classify_occupancy_transitions(sqs, ref, scores)
    vac_sqs = {sq for _, sq, _ in vacated}
    gain_sqs = {sq for _, sq, _ in gained}
    changed_set = set(changed_indices)

    pairs = []
    for frm, to in ((sq1, sq2), (sq2, sq1)):
        if not is_moving_side_piece(frm):
            continue
        if not is_legal_move(frm, to):
            continue
        fi, ti = chess_to_grid(frm), chess_to_grid(to)
        bonus = 0
        if frm in vac_sqs:
            bonus += 5000
        if to in gain_sqs:
            bonus += 5000
        if fi in changed_set and ti in changed_set:
            bonus += scores[fi] + scores[ti]
        pairs.append((bonus, frm, to))

    if not pairs:
        return None, None

    pairs.sort(key=lambda x: -x[0])
    return pairs[0][1], pairs[0][2]

def capture_engine_promo_for_move(frm, to):
    """Save engine promotion suggestion before apply_move clears the hint."""
    global promotion_suggested
    if engine_hint_frm == frm and engine_hint_to == to and engine_hint_promo:
        promotion_suggested = engine_hint_promo
    else:
        promotion_suggested = None

def try_apply_detected_move(frm, to):
    if is_en_passant_move(frm, to):
        if apply_en_passant(frm, to):
            set_ep_overlays(frm, to)
            return True
    elif is_legal_move(frm, to):
        capture_engine_promo_for_move(frm, to)
        if apply_move(frm, to):
            check_promotion(frm, to)
            return True
    return False

def process_move_detection(scores, sqs, ref):
    """
    Full move pipeline: castle -> filter noise -> en passant -> normal move.
    Returns (success, frm, to, overlay_indices)
    """
    if try_castle_detection(scores, sqs, ref):
        return True, None, None, list(overlay_indices)

    raw_strong = all_changed_squares(scores)
    if len(raw_strong) < 2:
        vacated, gained = classify_occupancy_transitions(sqs, ref, scores)
        for i, _, sc in vacated + gained:
            if i not in raw_strong and sc >= CHANGE_SCORE_THRESHOLD * 0.65:
                raw_strong.append(i)
    if not raw_strong:
        return False, None, None, []

    filtered = filter_pawn_skip_squares(raw_strong, scores)
    filtered = filter_sliding_path_squares(filtered, scores)

    if len(filtered) > 5:
        vacated, gained = classify_occupancy_transitions(sqs, ref, scores)
        keep = {i for i, _, _ in vacated} | {i for i, _, _ in gained}
        for idx in sorted(filtered, key=lambda i: -scores[i])[:4]:
            keep.add(idx)
        castle_subset = any(
            p.issubset({grid_to_chess(i) for i in filtered if grid_to_chess(i)})
            for p in CASTLE_SQUARE_SETS
        )
        if not castle_subset:
            filtered = [i for i in filtered if i in keep]

    if try_castle_from_changes(filtered, scores):
        return True, None, None, filtered

    if try_en_passant_from_changes(filtered, scores):
        return True, None, None, filtered

    frm, to, overlay = collect_move_candidates(filtered, scores, sqs, ref)
    if frm and to and try_apply_detected_move(frm, to):
        set_move_overlays(frm, to)
        print(f"{last_piece}: {frm}->{to}")
        return True, frm, to, overlay or filtered

    frm, to = fallback_two_square_detect(filtered, scores, sqs, ref)
    if frm and to and try_apply_detected_move(frm, to):
        set_move_overlays(frm, to)
        print(f"{last_piece}: {frm}->{to} (fallback)")
        return True, frm, to, filtered

    return False, frm, to, filtered

# ---------- MAPPING (camera grid idx <-> standard chess sq) ----------
# WHITE view: TL h8, TR h1, BL a8, BR a1
# BLACK view: TL a1, TR a8, BL h1, BR h8
def mapping_ready():
    return board_perspective in ("WHITE", "BLACK")

def grid_to_chess(idx):
    if not mapping_ready():
        return None
    row, col = idx // 8, idx % 8
    if board_perspective == "BLACK":
        return f"{chr(97 + row)}{col + 1}"
    return f"{chr(97 + (7 - row))}{8 - col}"

def chess_to_grid(sq):
    if not mapping_ready():
        return None
    sq = sq.lower()
    if len(sq) != 2 or sq[0] not in "abcdefgh" or sq[1] not in "12345678":
        return None
    f = ord(sq[0]) - 97
    r = int(sq[1])
    if board_perspective == "BLACK":
        return f * 8 + (r - 1)
    return (7 - f) * 8 + (8 - r)

def grid_to_board(idx):
    return grid_to_chess(idx)

def board_to_grid(sq):
    return chess_to_grid(sq)

def changed_chess_squares(grid_indices):
    squares = []
    for idx in grid_indices:
        sq = grid_to_chess(idx)
        if sq:
            squares.append(sq)
    return squares

def verify_mapping():
    for idx in range(64):
        sq = grid_to_chess(idx)
        back = chess_to_grid(sq)
        if back != idx:
            print(f"Mapping error: grid {idx} -> {sq} -> grid {back}")
            return False
    if board_perspective == "WHITE":
        expect = {0: "h8", 7: "h1", 56: "a8", 63: "a1"}
    else:
        expect = {0: "a1", 7: "a8", 56: "h1", 63: "h8"}
    for idx, sq in expect.items():
        if grid_to_chess(idx) != sq:
            print(f"Corner mismatch: grid {idx} is {grid_to_chess(idx)}, expected {sq}")
            return False
    return True

def set_board_perspective(side):
    global board_perspective
    board_perspective = side
    if verify_mapping():
        print(f"Grid mapping OK for {side} (all moves use chess coords a1-h8)")
    print(f"Corners — TL {grid_to_chess(0)}, TR {grid_to_chess(7)}, "
          f"BL {grid_to_chess(56)}, BR {grid_to_chess(63)}")
    print(f"Engine assists {side} — green highlight shows suggested move")
    refresh_engine_hint()
    robot_maybe_show_engine_move()

# ---------- CHESS ENGINE ----------
def find_stockfish():
    candidates = [
        STOCKFISH_PATH,
        shutil.which("stockfish"),
        shutil.which("stockfish.exe"),
        os.path.join(os.path.dirname(os.path.abspath(__file__)), "stockfish.exe"),
        os.path.join(os.path.dirname(os.path.abspath(__file__)), "stockfish", "stockfish.exe"),
        r"C:\Program Files\Stockfish\stockfish.exe",
    ]
    for path in candidates:
        if path and os.path.isfile(path):
            return path
    return None

def init_engine():
    global chess_engine, engine_status
    if not CHESS_LIB_OK:
        engine_status = "pip install chess"
        print("Install python-chess: pip install chess")
        return False
    path = find_stockfish()
    if not path:
        engine_status = "Stockfish not found"
        print("Stockfish not found — place stockfish.exe in project folder or set STOCKFISH_PATH")
        return False
    try:
        chess_engine = chess.engine.SimpleEngine.popen_uci(path)
        engine_status = f"Engine ready ({os.path.basename(path)})"
        print(engine_status)
        return True
    except Exception as exc:
        chess_engine = None
        engine_status = f"Engine error: {exc}"
        print(engine_status)
        return False

def castling_fen():
    rights = ""
    if board_state.get("e1") == "K" and board_state.get("h1") == "R":
        rights += "K"
    if board_state.get("e1") == "K" and board_state.get("a1") == "R":
        rights += "Q"
    if board_state.get("e8") == "k" and board_state.get("h8") == "r":
        rights += "k"
    if board_state.get("e8") == "k" and board_state.get("a8") == "r":
        rights += "q"
    return rights or "-"

def board_to_fen():
    rows = []
    for rank in range(8, 0, -1):
        row = ""
        empty = 0
        for file in "abcdefgh":
            piece = board_state.get(f"{file}{rank}", "")
            if not piece:
                empty += 1
            else:
                if empty:
                    row += str(empty)
                    empty = 0
                row += piece
        if empty:
            row += str(empty)
        rows.append(row)
    active = "w" if turn == "WHITE" else "b"
    ep = ep_target if ep_target else "-"
    return f"{'/'.join(rows)} {active} {castling_fen()} {ep} 0 1"

def clear_engine_hint():
    global engine_hint_frm, engine_hint_to, engine_hint_promo
    engine_hint_frm = None
    engine_hint_to = None
    engine_hint_promo = None

def refresh_engine_hint():
    global engine_hint_frm, engine_hint_to, engine_hint_promo, engine_status

    clear_engine_hint()
    if not mapping_ready() or chess_engine is None:
        return
    if turn != board_perspective:
        return

    try:
        fen = board_to_fen()
        board = chess.Board(fen)
        if board.is_game_over():
            engine_status = "Game over"
            return
        result = chess_engine.play(board, chess.engine.Limit(time=ENGINE_TIME_LIMIT))
        move = result.move
        if not move:
            return
        uci = move.uci()
        engine_hint_frm = chess.square_name(move.from_square)
        engine_hint_to = chess.square_name(move.to_square)
        engine_hint_promo = uci[4].upper() if len(uci) > 4 else None
        promo_txt = f"={engine_hint_promo}" if engine_hint_promo else ""
        engine_status = f"Play {engine_hint_frm}{engine_hint_to}{promo_txt}"
        print(f"Engine ({board_perspective}): {engine_status}")
    except Exception as exc:
        engine_status = f"Engine: {exc}"
        print(engine_status)

def on_board_changed():
    refresh_engine_hint()
    robot_maybe_show_engine_move()

# ---------- ROBOT MOTION ----------
def robot_set_status(text):
    global robot_status
    robot_status = text
    print(f"[Robot] {text}")

def robot_clamp_z(z):
    return max(float(z), ROBOT_Z_MIN)

def robot_send(cmd):
    if robot_ser is None:
        raise RuntimeError("Serial not connected")
    with robot_lock:
        robot_ser.write((cmd + "\n").encode())
    print("Sent:", cmd)

def robot_read_line(timeout=0.1):
    with robot_lock:
        old = robot_ser.timeout
        robot_ser.timeout = timeout
        try:
            return robot_ser.readline().decode(errors="ignore").strip()
        finally:
            robot_ser.timeout = old

def robot_drain(max_lines=100):
    with robot_lock:
        old = robot_ser.timeout
        robot_ser.timeout = 0.05
        try:
            for _ in range(max_lines):
                if not robot_ser.in_waiting:
                    break
                line = robot_ser.readline().decode(errors="ignore").strip()
                if line:
                    print("Drain:", line)
        finally:
            robot_ser.timeout = old

def robot_wait_idle(timeout=15):
    start = time.time()
    last_ok = None
    while time.time() - start < timeout:
        line = robot_read_line(timeout=0.05)
        if line:
            print("Recv:", line)
            if "busy" in line.lower():
                continue
            if "ok" in line.lower():
                last_ok = time.time()
        if last_ok and (time.time() - last_ok > 0.35):
            robot_drain()
            time.sleep(0.15)
            return True
    return False

def robot_parse_m114(response):
    text = response
    idx = response.lower().find("count")
    if idx >= 0:
        text = response[:idx]
    parsed = {}
    for axis in ("X", "Y", "Z"):
        m = re.search(rf"\b{axis}:\s*([-+]?\d+(?:\.\d+)?)", text, re.IGNORECASE)
        if m:
            parsed[axis] = float(m.group(1))
    return parsed

def robot_query_position(cmd="M114 R", timeout=2.5):
    with robot_lock:
        old = robot_ser.timeout
        robot_ser.timeout = 0.05
        try:
            while robot_ser.in_waiting:
                robot_ser.readline()
        finally:
            robot_ser.timeout = old
        robot_ser.write((cmd + "\n").encode())
        print("Sent:", cmd)
        parts = []
        start = time.time()
        got_axes = False
        while time.time() - start < timeout:
            robot_ser.timeout = 0.12
            raw = robot_ser.readline().decode(errors="ignore")
            if not raw:
                if got_axes and (time.time() - start > 0.25):
                    break
                continue
            line = raw.strip()
            if line:
                print("Recv:", line)
                parts.append(line)
            if len(robot_parse_m114(" ".join(parts))) == 3:
                got_axes = True
            if line.lower() == "ok" and got_axes:
                break
            if got_axes and (time.time() - start > 0.5):
                break
        robot_ser.timeout = old
        return " ".join(parts)

def robot_update_position(after_home=False):
    if after_home:
        time.sleep(0.25)
    for cmd in ("M114 R", "M114"):
        parsed = robot_parse_m114(robot_query_position(cmd))
        if len(parsed) == 3:
            parsed["Z"] = robot_clamp_z(parsed["Z"])
            robot_pos.update(parsed)
            return True
    if after_home:
        robot_pos.update({"X": 0.0, "Y": 0.0, "Z": ROBOT_Z_MIN})
        return True
    return False

def robot_probe_stow():
    robot_send("M402")
    robot_wait_idle()

def robot_go_z(z):
    z = robot_clamp_z(z)
    robot_send("G90")
    robot_wait_idle()
    robot_send(f"G1 Z{z} F3000")
    robot_wait_idle()
    robot_pos["Z"] = z

def robot_go_xy(x, y):
    robot_probe_stow()
    robot_send("G90")
    robot_wait_idle()
    robot_send(f"G1 X{x:.3f} Y{y:.3f} F3000")
    robot_wait_idle()
    robot_probe_stow()
    robot_pos["X"] = x
    robot_pos["Y"] = y
    if robot_pos["Z"] < ROBOT_Z_MIN:
        robot_go_z(ROBOT_Z_MIN)

def robot_go_photo():
    robot_probe_stow()
    robot_send("G90")
    robot_wait_idle()
    z = robot_clamp_z(max(robot_pos.get("Z", ROBOT_Z_MIN), ROBOT_PHOTO_Z))
    robot_send(f"G1 Z{z} F3000")
    robot_wait_idle()
    robot_send(f"G1 X{ROBOT_PHOTO_X:.3f} Y{ROBOT_PHOTO_Y:.3f} F3000")
    robot_wait_idle()
    robot_probe_stow()
    robot_pos.update({"X": ROBOT_PHOTO_X, "Y": ROBOT_PHOTO_Y, "Z": z})
    robot_update_position()

def robot_chess_sq_to_row_col(sq):
    sq = sq.lower()
    file, rank = sq[0], int(sq[1])
    if board_perspective == "BLACK":
        col = ord(file) - ord("a")
        row = 8 - rank
    else:
        col = ord("h") - ord(file)
        row = rank - 1
    return row, col

def robot_chess_sq_to_xy(sq):
    row, col = robot_chess_sq_to_row_col(sq)
    x = ROBOT_ORIGIN_X + col * ROBOT_BOARD_STEP + ROBOT_SQUARE_X_OFFSET
    move_row = 7 - row
    y = ROBOT_ORIGIN_Y + move_row * ROBOT_BOARD_STEP
    return x, y

def robot_worker_loop():
    while True:
        job = robot_queue.get()
        if job is None:
            robot_queue.task_done()
            break
        global robot_busy
        robot_busy = True
        try:
            job()
        except Exception as exc:
            robot_set_status(f"Error: {exc}")
        finally:
            robot_busy = False
            robot_queue.task_done()

def robot_enqueue(job):
    if robot_ser is None:
        robot_set_status("Robot offline — install pyserial / check COM3")
        return
    try:
        robot_queue.put_nowait(job)
    except queue.Full:
        robot_set_status("Robot busy — queue full")

def robot_disable_steppers():
    def job():
        global robot_state
        robot_send("M18")
        robot_wait_idle()
        robot_state = "DISABLED"
        robot_set_status("Steppers disabled — click Auto Home")
    robot_enqueue(job)

def robot_auto_home():
    def job():
        global robot_state
        robot_set_status("Homing...")
        robot_probe_stow()
        robot_send("G28")
        robot_wait_idle(timeout=90)
        robot_send("G90")
        robot_wait_idle()
        robot_pos.update({"X": 0.0, "Y": 0.0, "Z": 0.0})
        robot_update_position(after_home=True)
        robot_set_status("Homed — moving to photo position...")
        robot_go_photo()
        robot_state = "AT_PHOTO_SETUP"
        global ui_phase
        ui_phase = UI_PLACE_PIECES
        robot_set_status("Place pieces on the board, then press R")
    robot_enqueue(job)

def robot_confirm_setup():
    global robot_state, ui_phase
    if robot_state != "AT_PHOTO_SETUP" and ui_phase != UI_PLACE_PIECES:
        return
    robot_state = "READY"
    ui_phase = UI_CHESS
    try:
        open_chess_ui()
    except Exception as exc:
        print(f"open_chess_ui error: {exc}")
        robot_set_status(f"UI error: {exc}")
    robot_set_status("Ready — click 4 corners on Feed, select color, then play")
    show_transient_popup("Setup complete — select 4 board corners on Feed", 3.0)
    try:
        robot_maybe_show_engine_move()
    except Exception as exc:
        print(f"Robot hint move skipped: {exc}")

def robot_run_engine_move(frm, to):
    def job():
        global last_robot_move
        if not mapping_ready():
            robot_set_status("Select WHITE or BLACK first")
            return
        if turn != board_perspective:
            robot_set_status(f"Not {board_perspective}'s turn — no robot move")
            return
        fx, fy = robot_chess_sq_to_xy(frm)
        tx, ty = robot_chess_sq_to_xy(to)
        last_robot_move = (frm, to)
        robot_set_status(f"Moving to FROM {frm} ({fx:.1f}, {fy:.1f})...")
        robot_go_xy(fx, fy)
        time.sleep(ROBOT_DWELL_SEC)
        robot_set_status(f"Moving to TO {to} ({tx:.1f}, {ty:.1f})...")
        robot_go_xy(tx, ty)
        time.sleep(ROBOT_DWELL_SEC)
        robot_set_status("Returning to photo position...")
        robot_go_photo()
        robot_set_status(f"At photo — suggested {frm}{to} (Q=repeat)")
    robot_enqueue(job)

def robot_maybe_show_engine_move(force=False):
    global suppress_robot_after_undo
    if suppress_robot_after_undo and not force:
        suppress_robot_after_undo = False
        return
    if robot_state != "READY" or not mapping_ready():
        return
    if turn != board_perspective or promotion_mode:
        return
    if not engine_hint_frm or not engine_hint_to:
        return
    key = (engine_hint_frm, engine_hint_to)
    if not force and key == last_robot_move and robot_busy:
        return
    if robot_busy and not force:
        return
    robot_run_engine_move(engine_hint_frm, engine_hint_to)

def robot_repeat_last_move():
    frm, to = last_robot_move
    if not frm or not to:
        robot_set_status("No previous engine move to repeat")
        return
    if engine_hint_frm and engine_hint_to:
        frm, to = engine_hint_frm, engine_hint_to
    robot_run_engine_move(frm, to)

def robot_home_click(x, y):
    hx1, hy1, hx2, hy2 = STARTUP_HOME_BTN
    return hx1 <= x <= hx2 and hy1 <= y <= hy2

def ensure_camera():
    global cap, camera_error
    if cap is None:
        cap = cv2.VideoCapture(IP_CAMERA_URL)
    if not cap.isOpened():
        camera_error = f"Camera unavailable: {IP_CAMERA_URL}"
        return False
    camera_error = ""
    return True

def ensure_feed_window():
    global feed_window_ready, setup_window_closed
    ensure_camera()
    if not feed_window_ready:
        cv2.namedWindow("Feed", cv2.WINDOW_NORMAL)
        feed_window_ready = True
        if not setup_window_closed:
            try:
                cv2.destroyWindow("Chess Robot Setup")
            except cv2.error:
                pass
            setup_window_closed = True

def read_camera_frame():
    if not ensure_camera():
        img = np.full((480, 640, 3), 30, dtype=np.uint8)
        cv2.putText(img, "Camera not connected", (120, 220),
                    cv2.FONT_HERSHEY_SIMPLEX, 0.8, (0, 0, 255), 2)
        cv2.putText(img, camera_error[:55], (40, 260),
                    cv2.FONT_HERSHEY_SIMPLEX, 0.48, (180, 180, 180), 1)
        return False, img
    ok, frame = cap.read()
    if not ok or frame is None:
        img = np.full((480, 640, 3), 30, dtype=np.uint8)
        cv2.putText(img, "Camera read failed — retrying...", (100, 240),
                    cv2.FONT_HERSHEY_SIMPLEX, 0.75, (0, 200, 255), 2)
        return False, img
    return True, frame

def open_chess_ui():
    global chess_ui_ready
    if chess_ui_ready:
        return
    try:
        init_engine()
    except Exception as exc:
        print(f"Engine init warning: {exc}")
    ensure_feed_window()
    cv2.namedWindow("Chess", cv2.WINDOW_NORMAL)
    cv2.resizeWindow("Chess", DIGITAL_SIZE, DIGITAL_SIZE + DIGITAL_HEADER)
    chess_ui_ready = True

def draw_startup_screen():
    img = np.full((SETUP_H, SETUP_W, 3), 28, dtype=np.uint8)
    cv2.putText(img, "Chess Robot", (210, 80),
                cv2.FONT_HERSHEY_SIMPLEX, 1.2, (0, 200, 255), 2)
    cv2.putText(img, robot_status, (40, 140),
                cv2.FONT_HERSHEY_SIMPLEX, 0.65, (200, 200, 200), 1)
    cv2.putText(img, "Steppers disabled on startup", (40, 175),
                cv2.FONT_HERSHEY_SIMPLEX, 0.55, (160, 160, 160), 1)
    hx1, hy1, hx2, hy2 = STARTUP_HOME_BTN
    cv2.rectangle(img, (hx1, hy1), (hx2, hy2), (35, 35, 35), -1)
    cv2.rectangle(img, (hx1, hy1), (hx2, hy2), (0, 140, 255), 2)
    cv2.putText(img, "Auto Home", (hx1 + 95, hy1 + 42),
                cv2.FONT_HERSHEY_SIMPLEX, 0.85, (0, 200, 255), 2)
    cv2.putText(img, "Camera opens after homing (piece setup)", (40, 420),
                cv2.FONT_HERSHEY_SIMPLEX, 0.48, (120, 120, 120), 1)
    return img

def draw_place_pieces_overlay(frame):
    if frame is None:
        return np.full((480, 640, 3), 40, dtype=np.uint8)
    img = frame.copy()
    h, w = img.shape[:2]
    cv2.rectangle(img, (0, 0), (w, 90), (20, 20, 20), -1)
    cv2.putText(img, "Place pieces on the board", (20, 35),
                cv2.FONT_HERSHEY_SIMPLEX, 0.85, (0, 255, 255), 2)
    cv2.putText(img, "Head is at photo position — press R when ready", (20, 68),
                cv2.FONT_HERSHEY_SIMPLEX, 0.62, (200, 200, 200), 1)
    cv2.putText(img, robot_status[:60], (20, h - 20),
                cv2.FONT_HERSHEY_SIMPLEX, 0.48, (0, 180, 255), 1)
    return img

def click_setup(event, x, y, flags, param):
    if event == cv2.EVENT_LBUTTONDOWN and ui_phase == UI_STARTUP:
        if robot_home_click(x, y):
            robot_auto_home()

def draw_robot_panel(board):
    """No robot controls on chess board — setup is a separate phase."""
    pass

def init_robot():
    global robot_ser, robot_worker, robot_status, robot_state
    if not SERIAL_OK:
        robot_status = "pyserial missing — robot disabled"
        return
    try:
        robot_ser = serial.Serial(ROBOT_SERIAL_PORT, ROBOT_BAUD, timeout=0.1)
        time.sleep(2)
        robot_worker = threading.Thread(target=robot_worker_loop, daemon=True)
        robot_worker.start()
        robot_disable_steppers()
    except Exception as exc:
        robot_ser = None
        robot_status = f"Robot offline: {exc}"
        print(robot_status)

def shutdown_robot():
    if robot_worker is not None:
        robot_queue.put(None)
        robot_worker.join(timeout=2)
    if robot_ser is not None:
        robot_ser.close()

def draw_color_picker(board):
    cv2.rectangle(board, (80, 260), (720, 540), (25, 25, 25), -1)
    cv2.rectangle(board, (80, 260), (720, 540), (0, 200, 255), 2)
    cv2.putText(board, "Select your color (engine assists you)", (110, 300),
                cv2.FONT_HERSHEY_SIMPLEX, 0.85, (0, 200, 255), 2)

    wx1, wy1, wx2, wy2 = WHITE_BTN
    cv2.rectangle(board, (wx1, wy1), (wx2, wy2), (235, 235, 235), -1)
    cv2.rectangle(board, (wx1, wy1), (wx2, wy2), (0, 200, 255), 2)
    cv2.putText(board, "WHITE", (wx1 + 65, wy1 + 75),
                cv2.FONT_HERSHEY_SIMPLEX, 1.2, (20, 20, 20), 2)
    cv2.putText(board, "h8 TL", (wx1 + 70, wy1 + 105),
                cv2.FONT_HERSHEY_SIMPLEX, 0.45, (80, 80, 80), 1)

    bx1, by1, bx2, by2 = BLACK_BTN
    cv2.rectangle(board, (bx1, by1), (bx2, by2), (45, 45, 45), -1)
    cv2.rectangle(board, (bx1, by1), (bx2, by2), (0, 200, 255), 2)
    cv2.putText(board, "BLACK", (bx1 + 72, by1 + 75),
                cv2.FONT_HERSHEY_SIMPLEX, 1.2, (240, 240, 240), 2)
    cv2.putText(board, "a1 TL", (bx1 + 78, by1 + 105),
                cv2.FONT_HERSHEY_SIMPLEX, 0.45, (180, 180, 180), 1)

def color_picker_click(x, y):
    if board_perspective is not None:
        return False
    if ui_phase != UI_CHESS or robot_state != "READY":
        return False
    wx1, wy1, wx2, wy2 = WHITE_BTN
    if wx1 <= x <= wx2 and wy1 <= y <= wy2:
        set_board_perspective("WHITE")
        return True
    bx1, by1, bx2, by2 = BLACK_BTN
    if bx1 <= x <= bx2 and by1 <= y <= by2:
        set_board_perspective("BLACK")
        return True
    return False

# ---------- MANUAL MOVE ----------
def sq_to_idx(sq):
    return chess_to_grid(sq)

def parse_manual_move(text):
    text = text.strip().lower().replace(" ", "")
    if text in MANUAL_CASTLE_CODES:
        return "castle", text
    if len(text) == 4 and text[0] in "abcdefgh" and text[2] in "abcdefgh":
        if text[1] in "12345678" and text[3] in "12345678":
            return "move", (text[:2], text[2:])
    return None, None

def apply_manual_castle(code):
    global manual_input, manual_status, before_ref, failed_detect, castle_text

    squares = MANUAL_CASTLE_CODES.get(code)
    if not squares:
        manual_status = "Invalid castle code"
        failed_detect = True
        return False

    color = "WHITE" if code.startswith("w") else "BLACK"
    if turn != color:
        manual_status = f"Rejected — not {color}'s turn"
        failed_detect = True
        return False

    indices = [chess_to_grid(sq) for sq in squares]
    if None in indices or len(indices) != 4:
        manual_status = "Rejected — mapping not ready"
        failed_detect = True
        return False

    if not is_castle_legal(squares):
        manual_status = "Rejected — castling illegal"
        failed_detect = True
        return False

    msg = detect_castle(indices)
    if not msg:
        manual_status = "Rejected — castling illegal"
        failed_detect = True
        return False

    set_castle_overlays(indices, msg)
    manual_input = ""
    manual_status = ""
    failed_detect = False
    before_ref = None
    castle_text = msg
    show_transient_popup(f"{msg} — Press R to record pre-move frame", POPUP_DURATION)
    print(f"Manual castle: {msg}")
    return True

def set_move_overlays(frm, to):
    global overlay_indices, move_labels

    overlay_indices = []
    move_labels.clear()
    fi, ti = sq_to_idx(frm), sq_to_idx(to)
    if fi is not None:
        overlay_indices.append(fi)
        move_labels[fi] = "FROM"
    if ti is not None:
        overlay_indices.append(ti)
        move_labels[ti] = "TO"

def show_transient_popup(message, duration=POPUP_DURATION):
    global popup_text, popup_until
    popup_text = message
    popup_until = time.time() + duration

def clear_transient_popup():
    global popup_text, popup_until
    popup_text = ""
    popup_until = 0.0

def active_popup_message():
    if popup_text and time.time() <= popup_until:
        return popup_text
    return None

def draw_transient_popup(img):
    msg = active_popup_message()
    if not msg:
        return

    h, w = img.shape[:2]
    font = cv2.FONT_HERSHEY_SIMPLEX
    scale, thickness = 0.9, 2
    (tw, th), _ = cv2.getTextSize(msg, font, scale, thickness)
    pad_x, pad_y = 24, 20
    box_w = tw + pad_x * 2
    box_h = th + pad_y * 2
    x1 = max(10, (w - box_w) // 2)
    y1 = max(10, (h - box_h) // 2)
    x2, y2 = x1 + box_w, y1 + box_h

    overlay = img.copy()
    cv2.rectangle(overlay, (x1, y1), (x2, y2), (25, 25, 25), -1)
    cv2.addWeighted(overlay, 0.82, img, 0.18, 0, img)
    cv2.rectangle(img, (x1, y1), (x2, y2), (0, 200, 255), 3)
    cv2.putText(img, msg, (x1 + pad_x, y1 + pad_y + th - 4),
                font, scale, (0, 255, 255), thickness)

def sync_manual_overlays(text):
    global overlay_indices, move_labels

    text = text.strip().lower().replace(" ", "")
    overlay_indices = []
    move_labels.clear()

    if text in CASTLE_KING_MOVE:
        frm, to = CASTLE_KING_MOVE[text]
        for sq, label in [(frm, "FROM"), (to, "TO")]:
            idx = sq_to_idx(sq)
            if idx is not None:
                overlay_indices.append(idx)
                move_labels[idx] = label
        return

    if len(text) >= 2 and text[0] in "abcdefgh" and text[1] in "12345678":
        fi = sq_to_idx(text[:2])
        if fi is not None:
            overlay_indices.append(fi)
            move_labels[fi] = "FROM"

    if len(text) >= 4 and text[2] in "abcdefgh" and text[3] in "12345678":
        ti = sq_to_idx(text[2:4])
        if ti is not None:
            if ti not in overlay_indices:
                overlay_indices.append(ti)
            move_labels[ti] = "TO"

def apply_manual_move(text):
    global manual_input, manual_status, before_ref, failed_detect

    kind, data = parse_manual_move(text)
    if kind is None:
        manual_status = "Invalid — use e4e5 or wsc/wlc/bsc/blc"
        failed_detect = True
        return False

    if kind == "castle":
        return apply_manual_castle(data)

    frm, to = data
    set_move_overlays(frm, to)

    if is_en_passant_move(frm, to):
        if apply_en_passant(frm, to):
            set_move_overlays(frm, to)
            print(f"Manual En Passant: {frm} -> {to}")
            manual_input = ""
            manual_status = ""
            failed_detect = False
            before_ref = None
            show_transient_popup("Press R to record pre-move frame")
            return True

    capture_engine_promo_for_move(frm, to)
    if not apply_move(frm, to):
        in_chk = in_check(turn == "WHITE")
        if in_chk:
            manual_status = f"Rejected — {turn} is in check"
        else:
            manual_status = f"Rejected — illegal {turn} move {frm}->{to}"
        failed_detect = True
        return False

    print(f"Manual {last_piece}: {frm}->{to}")
    manual_input = ""
    manual_status = ""
    failed_detect = False
    check_promotion(frm, to)
    before_ref = None
    if promotion_mode:
        if not promotion_suggested:
            show_transient_popup(
                "Pick promotion piece — swap on board, then press R for pre-frame",
                3.0,
            )
    else:
        show_transient_popup("Press R to record pre-move frame")
    return True

# ---------- PROMOTION ----------
def draw_promotion_buttons(img, panel_x, panel_y, panel_w, btn_h):
    if not promotion_mode:
        return
    btn_w = panel_w // 4
    suggested = promotion_suggested
    if suggested:
        title = f"Promote {promotion_square} — engine: {piece_name(suggested)}"
    else:
        title = f"Promote {promotion_square}:"
    cv2.putText(img, title, (panel_x + 4, panel_y - 8),
                cv2.FONT_HERSHEY_SIMPLEX, 0.52, (0, 220, 255), 2)
    for i, (sym, name) in enumerate(zip(PROMO_CHOICES, PROMO_LABELS)):
        x1 = panel_x + i * btn_w
        y1, y2 = panel_y, panel_y + btn_h
        x2 = x1 + btn_w - 6
        highlight = suggested and sym == suggested.upper()
        cv2.rectangle(img, (x1, y1), (x2, y2), (35, 35, 35), -1)
        border = (0, 255, 255) if highlight else (0, 200, 255)
        thickness = 3 if highlight else 2
        cv2.rectangle(img, (x1, y1), (x2, y2), border, thickness)
        if highlight:
            cv2.putText(img, "GO", (x1 + btn_w // 2 - 16, y1 + 18),
                        cv2.FONT_HERSHEY_SIMPLEX, 0.45, (0, 255, 255), 1)
        cv2.putText(img, sym, (x1 + btn_w // 2 - 14, y1 + 38),
                    cv2.FONT_HERSHEY_SIMPLEX, 1.1, (0, 255, 255), 2)
        cv2.putText(img, name, (x1 + 8, y1 + btn_h - 10),
                    cv2.FONT_HERSHEY_SIMPLEX, 0.42, (190, 190, 190), 1)

def promotion_click(x, y, panel_x, panel_y, panel_w, btn_h):
    if not promotion_mode:
        return False
    if not (panel_y <= y <= panel_y + btn_h):
        return False
    btn_w = panel_w // 4
    for i, choice in enumerate(PROMO_CHOICES):
        x1 = panel_x + i * btn_w
        x2 = x1 + btn_w - 6
        if x1 <= x <= x2:
            apply_promotion(choice)
            return True
    return False

def check_promotion(frm, to):
    global promotion_mode, promotion_square, promotion_status, before_ref

    if not frm or not to:
        return False

    piece = board_state.get(to)

    if piece == "P" and to[1] == "8":
        promotion_mode = True
        promotion_square = to
        if promotion_suggested:
            promotion_status = (
                f"Pawn on {to} — engine suggests {piece_name(promotion_suggested)}; "
                f"pick piece, swap on board, then R"
            )
            show_transient_popup(
                f"Promotion: engine suggests {piece_name(promotion_suggested)} — click piece below",
                2.5,
            )
        else:
            promotion_status = f"Pawn on {to} — pick piece, swap on board, then R"
        before_ref = None
        print(f"Promotion needed on {to} — choose Queen, Rook, Bishop, or Knight")
        return True

    if piece == "p" and to[1] == "1":
        promotion_mode = True
        promotion_square = to
        if promotion_suggested:
            promotion_status = (
                f"Pawn on {to} — engine suggests {piece_name(promotion_suggested)}; "
                f"pick piece, swap on board, then R"
            )
            show_transient_popup(
                f"Promotion: engine suggests {piece_name(promotion_suggested)} — click piece below",
                2.5,
            )
        else:
            promotion_status = f"Pawn on {to} — pick piece, swap on board, then R"
        before_ref = None
        print(f"Promotion needed on {to} — choose Queen, Rook, Bishop, or Knight")
        return True

    return False

def apply_promotion(choice):
    global board_state, promotion_mode, promotion_square, last_piece
    global before_ref, promotion_status, promotion_suggested

    if not promotion_mode or choice not in PROMO_CHOICES:
        return False

    sq = promotion_square
    p = board_state.get(sq)
    if not p:
        return False

    save_snapshot()
    new_piece = choice if is_white(p) else choice.lower()
    board_state[sq] = new_piece
    last_piece = f"Promotion ({piece_name(new_piece)})"
    promotion_mode = False
    promotion_square = None
    promotion_suggested = None
    before_ref = None
    promotion_status = "Swap piece on board, then press R (pre-move)"
    show_transient_popup("Swap piece on board, then press R to record pre-move frame", 3.0)
    print(f"Promoted {sq} to {piece_name(new_piece)} — swap on board, then R for next move")
    on_board_changed()
    return True
# ---------- DRAW ----------
def draw(board):
    global promotion_mode

    if board_perspective is None:
        draw_color_picker(board)
        return board

    step=BOARD_SIZE//8

    cv2.putText(board,f"TURN: {turn}",(20,40),
                cv2.FONT_HERSHEY_SIMPLEX,1,(0,255,0),2)

    cv2.putText(board,f"VIEW: {board_perspective} (engine)",(400,40),
                cv2.FONT_HERSHEY_SIMPLEX,0.65,(180,180,180),2)

    if engine_status:
        cv2.putText(board, engine_status[:44], (20, 230),
                    cv2.FONT_HERSHEY_SIMPLEX, 0.55, (0, 220, 0), 2)

    piece_scale = 0.72 if len(last_piece) > 18 else 1.0
    cv2.putText(board, f"PIECE: {last_piece}", (20, 80),
                cv2.FONT_HERSHEY_SIMPLEX, piece_scale, (0, 200, 255), 2)

    cv2.putText(board,f"EP: {enpassant_text}",(20,120),
                cv2.FONT_HERSHEY_SIMPLEX,0.8,(255,255,0),2)

    if undo_status:
        cv2.putText(board, undo_status, (20, BOARD_SIZE - 20),
                    cv2.FONT_HERSHEY_SIMPLEX, 0.65, (0, 165, 255), 2)

    # ---------- MANUAL MOVE INPUT ----------
    bx1, by1, bx2, by2 = MANUAL_BOX
    cv2.rectangle(board, (bx1, by1), (bx2, by2), (30, 30, 30), -1)
    cv2.rectangle(board, (bx1, by1), (bx2, by2), (0, 200, 255), 2)
    cv2.putText(board, "Move:", (bx1 + 8, by1 + 22),
                cv2.FONT_HERSHEY_SIMPLEX, 0.55, (180, 180, 180), 1)
    display = manual_input + "|"
    cv2.putText(board, display, (bx1 + 58, by1 + 22),
                cv2.FONT_HERSHEY_SIMPLEX, 0.65, (0, 200, 255), 2)
    cv2.putText(board, "Enter=apply (wsc/wlc/bsc/blc)", (bx1 + 8, by2 - 8),
                cv2.FONT_HERSHEY_SIMPLEX, 0.45, (140, 140, 140), 1)
    if manual_status:
        cv2.putText(board, manual_status, (20, 160),
                    cv2.FONT_HERSHEY_SIMPLEX, 0.65, (0, 140, 255), 2)

    if promotion_status:
        cv2.putText(board, promotion_status, (20, 195),
                    cv2.FONT_HERSHEY_SIMPLEX, 0.58, (0, 220, 255), 2)

    draw_promotion_buttons(board, PROMO_PANEL_X, PROMO_PANEL_Y1,
                           BOARD_SIZE - 40, PROMO_PANEL_Y2 - PROMO_PANEL_Y1)

    for i in range(8):
        for j in range(8):
            idx=i*8+j
            x1, y1 = j * step, i * step
            x2, y2 = x1 + step, y1 + step

            cv2.rectangle(board, (x1, y1), (x2, y2), (70, 70, 70), 1)

            label = grid_to_chess(idx)
            if not label:
                continue
            tx, ty = x1 + 5, y2 - 6
            font, scale, thickness = cv2.FONT_HERSHEY_SIMPLEX, 0.42, 1
            (tw, th), _ = cv2.getTextSize(label, font, scale, thickness)
            cv2.rectangle(board, (tx - 2, ty - th - 3), (tx + tw + 3, ty + 3), (0, 0, 0), -1)
            cv2.putText(board, label, (tx, ty), font, scale, (180, 220, 180), thickness)

            if engine_hint_frm and engine_hint_to:
                for sq, lbl in ((engine_hint_frm, "GO"), (engine_hint_to, "GO")):
                    if chess_to_grid(sq) == idx:
                        cv2.rectangle(board, (x1, y1), (x2, y2), (0, 255, 0), 3)
                        cv2.putText(board, lbl, (x1 + 8, y1 + step - 10),
                                    cv2.FONT_HERSHEY_SIMPLEX, 0.75, (0, 255, 0), 2)

            if idx in overlay_indices:
                cv2.rectangle(board,(x1, y1), (x2, y2),(0,0,255),3)

                if idx in move_labels:
                    cv2.putText(board,move_labels[idx],
                                (x1+10, y1+step-10),
                                cv2.FONT_HERSHEY_SIMPLEX,0.8,(0,0,255),2)

    draw_transient_popup(board)
    return board

# ---------- DIGITAL BOARD PIECES (chess.com-style glyphs) ----------
PIECE_GLYPH = {
    "P": "\u2659", "N": "\u2658", "B": "\u2657", "R": "\u2656", "Q": "\u2655", "K": "\u2654",
    "p": "\u265F", "n": "\u265E", "b": "\u265D", "r": "\u265C", "q": "\u265B", "k": "\u265A",
}
_piece_img_cache = {}
_piece_font_path = None

def _find_piece_font():
    global _piece_font_path
    if _piece_font_path:
        return _piece_font_path
    candidates = [
        os.path.join(os.environ.get("WINDIR", "C:\\Windows"), "Fonts", "seguisym.ttf"),
        os.path.join(os.environ.get("WINDIR", "C:\\Windows"), "Fonts", "Segoe UI Symbol.ttf"),
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    ]
    for path in candidates:
        if os.path.isfile(path):
            _piece_font_path = path
            return path
    return None

def get_piece_image(piece, size):
    key = (piece, size)
    if key in _piece_img_cache:
        return _piece_img_cache[key]
    glyph = PIECE_GLYPH.get(piece)
    if not glyph or size < 8:
        return None
    try:
        from PIL import Image, ImageDraw, ImageFont
    except ImportError:
        return None
    try:
        font_path = _find_piece_font()
        if not font_path:
            return None
        font = ImageFont.truetype(font_path, max(12, int(size * 0.82)))
        img = Image.new("RGBA", (size, size), (0, 0, 0, 0))
        draw = ImageDraw.Draw(img)
        if hasattr(draw, "textbbox"):
            bbox = draw.textbbox((0, 0), glyph, font=font)
            tw, th = bbox[2] - bbox[0], bbox[3] - bbox[1]
            tx = (size - tw) // 2 - bbox[0]
            ty = (size - th) // 2 - bbox[1]
        else:
            tw, th = draw.textsize(glyph, font=font)
            tx = (size - tw) // 2
            ty = (size - th) // 2
        fill = (250, 250, 250, 255) if is_white(piece) else (35, 35, 35, 255)
        stroke = (25, 25, 25, 255) if is_white(piece) else (180, 180, 180, 255)
        try:
            draw.text((tx, ty), glyph, font=font, fill=fill,
                      stroke_width=max(1, size // 24), stroke_fill=stroke)
        except TypeError:
            draw.text((tx, ty), glyph, font=font, fill=fill)
        arr = np.array(img)
        _piece_img_cache[key] = arr
        return arr
    except Exception as exc:
        print(f"Piece render failed ({piece}): {exc}")
        return None

def blit_rgba(dst, rgba, x, y):
    h, w = rgba.shape[:2]
    H, W = dst.shape[:2]
    if x >= W or y >= H:
        return
    x2, y2 = min(W, x + w), min(H, y + h)
    w, h = x2 - x, y2 - y
    if w <= 0 or h <= 0:
        return
    roi = dst[y:y2, x:x2]
    src = rgba[:h, :w]
    alpha = src[:, :, 3:4].astype(np.float32) / 255.0
    roi[:] = (alpha * src[:, :, :3] + (1.0 - alpha) * roi).astype(np.uint8)

def digital_display_rank(display_row):
    """Row 0 = top of screen. Opponent pieces on bottom row."""
    if board_perspective == "WHITE":
        return display_row + 1
    return 8 - display_row

def digital_file_idx(display_col):
    """Column 0 = left of screen. WHITE view mirrors files (h..a left to right)."""
    if board_perspective == "WHITE":
        return 7 - display_col
    return display_col

def digital_square(display_row, display_col):
    rank = digital_display_rank(display_row)
    file_idx = digital_file_idx(display_col)
    return f"{chr(ord('a') + file_idx)}{rank}"

def digital_file_label(display_col):
    return chr(ord("a") + digital_file_idx(display_col))

def digital_rank_label(display_row):
    return str(digital_display_rank(display_row))

def square_is_light(file_idx, rank):
    return (file_idx + rank) % 2 == 0

# ---------- DIGITAL CHESS BOARD ----------
def draw_digital_board():
    try:
        return _draw_digital_board_impl()
    except Exception as exc:
        print(f"draw_digital_board error: {exc}")
        img = np.full((DIGITAL_SIZE + DIGITAL_HEADER, DIGITAL_SIZE, 3), 40, dtype=np.uint8)
        cv2.putText(img, "Chess board error", (12, 40),
                    cv2.FONT_HERSHEY_SIMPLEX, 0.7, (0, 0, 255), 2)
        cv2.putText(img, str(exc)[:40], (12, 70),
                    cv2.FONT_HERSHEY_SIMPLEX, 0.5, (200, 200, 200), 1)
        return img

def _draw_digital_board_impl():
    promo_h = 78 if promotion_mode else 0
    h = DIGITAL_SIZE + DIGITAL_HEADER + promo_h
    img = np.full((h, DIGITAL_SIZE, 3), 40, dtype=np.uint8)

    cv2.putText(img, f"{turn} to move", (12, 26),
                cv2.FONT_HERSHEY_SIMPLEX, 0.7, (0, 255, 120), 2)

    if board_perspective:
        opponent = "BLACK" if board_perspective == "WHITE" else "WHITE"
        cv2.putText(img, f"You: {board_perspective}  |  {opponent} at bottom", (12, 48),
                    cv2.FONT_HERSHEY_SIMPLEX, 0.48, (180, 180, 180), 1)
        status_y = 66
    else:
        status_y = 48
    status = promotion_status or engine_status or enpassant_text or last_piece or "—"
    cv2.putText(img, status[:46], (12, status_y),
                cv2.FONT_HERSHEY_SIMPLEX, 0.48, (200, 200, 200), 1)

    step = DIGITAL_SIZE // 8
    font = cv2.FONT_HERSHEY_SIMPLEX
    piece_px = int(step * 0.88)

    for display_row in range(8):
        for display_col in range(8):
            sq = digital_square(display_row, display_col)
            file_idx = digital_file_idx(display_col)
            x1 = display_col * step
            y1 = DIGITAL_HEADER + display_row * step
            x2, y2 = x1 + step, y1 + step

            cv2.rectangle(img, (x1, y1), (x2, y2),
                          LIGHT_SQ if square_is_light(file_idx, digital_display_rank(display_row))
                          else DARK_SQ, -1)

            piece = board_state.get(sq)
            if piece:
                pimg = get_piece_image(piece, piece_px)
                if pimg is not None:
                    if board_perspective == "WHITE":
                        pimg = np.fliplr(pimg)
                    ox = x1 + (step - piece_px) // 2
                    oy = y1 + (step - piece_px) // 2
                    blit_rgba(img, pimg, ox, oy)
                else:
                    color = (255, 255, 255) if is_white(piece) else (25, 25, 25)
                    outline = (0, 0, 0) if is_white(piece) else (255, 255, 255)
                    sym = PIECE_GLYPH.get(piece, piece.upper())
                    cx, cy = x1 + step // 2 - 10, y1 + step // 2 + 10
                    cv2.putText(img, sym, (cx, cy), font, 1.1, outline, 3)
                    cv2.putText(img, sym, (cx, cy), font, 1.1, color, 1)

            if promotion_mode and sq == promotion_square:
                cv2.rectangle(img, (x1, y1), (x2, y2), (0, 200, 255), 3)

    for i in range(8):
        cv2.putText(img, digital_file_label(i),
                    (i * step + step // 2 - 6, DIGITAL_HEADER + DIGITAL_SIZE - 6),
                    font, 0.45, (160, 160, 160), 1)

    for display_row in range(8):
        cv2.putText(img, digital_rank_label(display_row),
                    (4, DIGITAL_HEADER + display_row * step + step // 2 + 5),
                    font, 0.45, (160, 160, 160), 1)

    if promotion_mode:
        draw_promotion_buttons(img, 0, DIGITAL_SIZE + DIGITAL_HEADER,
                               DIGITAL_SIZE, 68)

    draw_transient_popup(img)
    return img

# ---------- MAIN ----------
try:
    init_robot()
except Exception as exc:
    print(f"Robot init error: {exc}")
    robot_status = f"Robot init error: {exc}"
cv2.namedWindow("Chess Robot Setup", cv2.WINDOW_NORMAL)
cv2.resizeWindow("Chess Robot Setup", SETUP_W, SETUP_H)
cv2.setMouseCallback("Chess Robot Setup", click_setup)

def click_feed(e, x, y, f, p):
    global points, selected

    if e == cv2.EVENT_LBUTTONDOWN:
        if len(points) < 4:
            points.append((x, y))
        if len(points) == 4:
            selected = True
            if cap is not None:
                ok, frame = cap.read()
                if ok:
                    cv2.namedWindow("Board", cv2.WINDOW_NORMAL)
                    cv2.resizeWindow("Board", BOARD_SIZE, BOARD_SIZE)
                    cv2.imshow("Board", draw(warp_board(frame, points)))
                    cv2.setMouseCallback("Board", click_board)
                    cv2.waitKey(1)

def click_board(e, x, y, f, p):
    if e == cv2.EVENT_LBUTTONDOWN:
        if color_picker_click(x, y):
            return
        promotion_click(x, y, PROMO_PANEL_X, PROMO_PANEL_Y1,
                        BOARD_SIZE - 40, PROMO_PANEL_Y2 - PROMO_PANEL_Y1)

def click_chess(e, x, y, f, p):
    if e == cv2.EVENT_LBUTTONDOWN:
        promotion_click(x, y, 0, DIGITAL_SIZE + DIGITAL_HEADER, DIGITAL_SIZE, 68)

def capture_board_samples(cap, points, n=CAPTURE_FRAMES):
    samples = []
    if cap is None:
        return samples
    for _ in range(n):
        time.sleep(CAPTURE_DELAY)
        ok, frame = cap.read()
        if ok:
            samples.append(split_grid(warp_board(frame, points)))
    return samples

while True:
    k = cv2.waitKey(1) & 0xFF

    if ui_phase == UI_STARTUP:
        cv2.imshow("Chess Robot Setup", draw_startup_screen())
    elif ui_phase == UI_PLACE_PIECES:
        ensure_feed_window()
        if not feed_callbacks_bound:
            cv2.setMouseCallback("Feed", click_feed)
            feed_callbacks_bound = True
        ok, frame = read_camera_frame()
        cv2.imshow("Feed", draw_place_pieces_overlay(frame))
        if k == ord("r"):
            robot_confirm_setup()
    elif ui_phase == UI_CHESS:
        ensure_feed_window()
        if not feed_callbacks_bound:
            cv2.setMouseCallback("Feed", click_feed)
            feed_callbacks_bound = True
        if chess_ui_ready and not chess_callbacks_bound:
            cv2.setMouseCallback("Chess", click_chess)
            chess_callbacks_bound = True
        ok, frame = read_camera_frame()
        cv2.imshow("Feed", frame)
        if chess_ui_ready:
            cv2.imshow("Chess", draw_digital_board())
            chess_h = DIGITAL_SIZE + DIGITAL_HEADER + (78 if promotion_mode else 0)
            cv2.resizeWindow("Chess", DIGITAL_SIZE, chess_h)
        if selected and ok:
            b = warp_board(frame, points)
            cv2.imshow("Board", draw(b.copy()))

        if k == ord("r") and selected:
            if board_perspective is None:
                print("Select WHITE or BLACK on the Board window first")
                continue
            if promotion_mode:
                print("Select promotion piece first (Queen / Rook / Bishop / Knight)")
                continue

            samples = capture_board_samples(cap, points)
            if not samples:
                continue
            sqs = samples[-1]
            curr = capture_ref_averaged(samples)

            if before_ref is None:
                before_ref = curr
                clear_transient_popup()
                undo_status = ""
                manual_status = ""
                promotion_status = ""
                print("Reference set (pre-move). Press R again after the move.")
            else:
                scores = compute_change_robust(samples, before_ref)
                enpassant_text = ""
                undo_status = ""
                manual_status = ""
                failed_detect = False

                ok_move, chess_frm, chess_to, _ = process_move_detection(scores, sqs, before_ref)

                if ok_move:
                    failed_detect = False
                else:
                    castle_text = ""
                    if chess_frm and chess_to:
                        if in_check(turn == "WHITE"):
                            manual_status = f"Illegal — {turn} in check, must address it"
                        else:
                            manual_status = f"Detect failed — try {chess_frm}{chess_to} + Enter"
                        set_move_overlays(chess_frm, chess_to)
                        failed_detect = True
                    elif all_changed_squares(scores):
                        manual_status = "Detect failed — type move e.g. d7d5 + Enter"
                        failed_detect = True
                    else:
                        manual_status = "No change detected — re-capture pre-move (R)"
                        failed_detect = True

                if not promotion_mode and ok_move:
                    before_ref = curr

        elif k == ord("q") and robot_state == "READY":
            robot_repeat_last_move()

        elif k == ord("u") and selected and mapping_ready():
            if failed_detect:
                undo_failed_detect()
            else:
                undo_last()

        elif selected and mapping_ready() and k in (8, 127):
            manual_input = manual_input[:-1]
            manual_status = ""
            sync_manual_overlays(manual_input)

        elif selected and mapping_ready() and k in (13, 10):
            apply_manual_move(manual_input)

        elif selected and mapping_ready() and 0 < k < 128 and chr(k).isalnum():
            if len(manual_input) < 8:
                manual_input += chr(k).lower()
                manual_status = ""
                sync_manual_overlays(manual_input)

    if k == 27:
        break

if chess_engine:
    chess_engine.quit()

shutdown_robot()
if cap is not None:
    cap.release()
cv2.destroyAllWindows() 