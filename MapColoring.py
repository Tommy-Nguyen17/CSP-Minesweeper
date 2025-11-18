# File: MapColoring.py
# Author: Chad Hogg
# An example of how Z3 can be used to set up and solve a map-coloring problem.
# Interesting variations:
# (1) Try removing green as an option, and you'll find the problem to be unsolvable
# (2) Try adding another territory "ocean" connected to all existing territories, and you'll find the problem unsolvable with three colors

# Necessary to use the Z3 library.
import z3

# Variables for the territories that need to be colored.
# We are creating Int-type z3 variables because they are easiest to work with
WA, NT, Q, SA, NSW, V, T = z3.Ints('WA NT Q SA NSW V T')

# This dictionary lets we refer to these variables using human-readable names later.
# It's also convenient that the keys of this dictionary give me the full set of variables.
TERRITORY_NAMES = {WA: "Western Australia", 
                   NT: "Northern Territory", 
                   Q: "Queensland", 
                   SA: "South Australia", 
                   NSW: "New South Wales", 
                   V: "Victoria", 
                   T: "Tazmania"}

# The colors we are willing to try using on the map.
# You can add / remove from this dictionary.
COLOR_NAMES = {1: "red", 
               2: "blue", 
               3: "green"}

# Create a solver
solver = z3.Solver()

# Force every variable to be assigned to one of the "colors".
for var in TERRITORY_NAMES.keys():
    solver.add(z3.Or([var == value for value in COLOR_NAMES.keys()]))

# Territories that touch cannot be the same color.
solver.add(WA != NT)
solver.add(WA != SA)
solver.add(NT != Q)
solver.add(NT != SA)
solver.add(Q != SA)
solver.add(Q != NSW)
solver.add(SA != NSW)
solver.add(SA != V)
solver.add(NSW != V)

# Try solving the problem.
possible = solver.check()
if possible == z3.sat:
    model = solver.model()
    for var in TERRITORY_NAMES.keys():
        print(TERRITORY_NAMES[var] + " gets color " + str(COLOR_NAMES[model[var].as_long()]))
else:
    print("There is no way to assign each territory to one of the the " + str(len(COLOR_NAMES)) + " colors")
