# Computer-Vision-Chess-Robot
I used the XYZ movements of my 3d Printer and computer vision to assess an active chess position and use g code to manipulate the print head to indicate what move should be made.
I attached a phone holder on the filament stand of my 3D Printer. I used a webcam app on the phone to get live footage from it. I then ran that footage through opencv in python to analyse the moves that are being made.
A huge part of this was trying to figure out the correct color scheme for the board, so that it has enough contrast with the pieces so it can detect moves reliably. 
I then linked the detected moves to stockfish to detect the legality of moves and suggest the best move for a given scenario.
I then used serial ports to output G Code to the printer to dictate movements to and from and particular square. 
Along with this, I wired a resistor and LED to a perf board and attached it to the printhead to act as a spotlight.

<img width="402" height="306" alt="image" src="https://github.com/user-attachments/assets/39fbf52b-dc5a-4f62-8e3e-66353b09081c" />

https://github.com/user-attachments/assets/32b38799-6db7-4bfa-8073-f15ee750384c
