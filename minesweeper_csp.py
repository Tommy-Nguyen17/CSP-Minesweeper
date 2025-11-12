# Project by Paige Althoff, Andrew Elko & Tommy Nguyen

# Import necessary to use the Z3 Library
import z3

"""

Modelling a 5x5 Minesweeper board:

instance = ((? ? 1 ? 1 )
            (1 ? ? ? ? )
            (? ? 0 ? ? )
            (? ? ? ? 1 )
            (2 ? 1 ? ? ))

"""

solver = z3.Solver()

