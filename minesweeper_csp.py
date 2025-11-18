# Project by Paige Althoff, Andrew Elko & Tommy Nguyen

# Import necessary to use the Z3 Library
import z3

"""

Modelling a 5x5 Minesweeper board:

#Fresh Board with No Info
instance = ((? ? ? ? ?)
            (? ? ? ? ?)
            (? ? ? ? ?)
            (? ? ? ? ?)
            (? ? ? ? ?))

instance = ((? ? 1 1 ? )
            (? 2 ? ? ? )
            (2 ? ? 2 ? )
            (2 ? ? 2 1 )
            (? 2 2 1 ? ))

"""

# Provable function that checks if that statement can be proven
# TODO

# Create the solver
solver = z3.Solver()

hasMine = []
numberSpace = []

# Need number space info somehow
for row in range(0, 5):
    hasMine.append([])
    numberSpace.append([])
    for col in range (0, 5):
        hasMine[row].append(z3.Bool("*" + str(row) + str(col)))
        numberSpace[row].append(z3.Bool("_" + str(row) + str(col)))

# Background knowledge about what the numbers mean.
for row in range(0, 5):
    for col in range(0, 5):
        mine_neighbors = []
        if row > 0: mine_neighbors.append(hasMine[row - 1][col])
        if row < 4: mine_neighbors.append(hasMine[row + 1][col])
        if col > 0: mine_neighbors.append(hasMine[row][col - 1])
        if col < 4: mine_neighbors.append(hasMine[row][col + 1])
        if row > 0 and col > 0: mine_neighbors.append(hasMine[row - 1][col - 1])
        if row > 0 and col < 4: mine_neighbors.append(hasMine[row - 1][col + 1])
        if row < 4 and col > 0: mine_neighbors.append(hasMine[row + 1][col - 1])
        if row < 4 and col < 4: mine_neighbors.append(hasMine[row + 1][col + 1])
        # If a space is a number space, it can't have a mine
        solver.add(z3.Implies(numberSpace[row][col], z3.Not(hasMine[row][col])))
        # If a square has a number, there are that many mines adjacent to it
        solver.add(z3.Implies(numberSpace[row][col], z3.Or(mine_neighbors)))

print("On this board, _ marks a square definitely doesn't contain a mine")
print("\tand * marks a square that definitely contains a mine,")
print("\twhile a number tells you how many mines are adjacent to that square")

answer = "Ford the River"
while answer != "Q":
    # Print out stuff we know about the adjacent squares
    # TODO

    print("You are exploring a grid of rows 0-4 and columns 0-4.")
    print("Please type in one of the following:")
    # Type in info about the thingy
    print("\t2 0 1 if there are 2 mines adjacent to row 0 column 1")
    print("\tQ if you wish to exit because you won / died / got bored")

    # Find out what happened at this time step.
    answer = input("Your current knowledge: ")

    # Adding constraints to the solver
    if len(answer) == 5 and answer[0] in ["0", "1", "2", "3", "4", "5", "6", "7", "8"] and answer[1] == " " and answer [3] == " " and answer[2] in ["0", "1", "2", "3", "4"] and answer[4] in ["0", "1", "2", "3", "4"]:
        # TODO
        pass
    elif answer != "Q":
        print("Your response was not understood.")
    print()