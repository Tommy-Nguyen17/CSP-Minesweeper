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

# Provable function that checks if that statement can be proven (proof by contradiction)
def provable(z3solver: z3.Solver, statement: z3.z3.BoolRef):
    z3solver.push()
    z3solver.add(z3.Not(statement))
    result = z3solver.check() == z3.unsat
    z3solver.pop()
    return result

# Create the solver
solver = z3.Solver()

hasMine = []
numberSpace = []
# For printing the board
user_input = []

# Need number space info somehow
for row in range(0, 5):
    hasMine.append([])
    numberSpace.append([])
    user_input.append([])
    for col in range (0, 5):
        hasMine[row].append(z3.Bool("*" + str(row) + str(col)))
        numberSpace[row].append(z3.Int(str(row) + str(col)))
        user_input[row].append(None)

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
        solver.add(z3.Implies(numberSpace[row][col] >= 0, z3.Not(hasMine[row][col])))
        # If a square has a number, there are exactly that many mines adjacent to it
        num_neighbors_w_mines = z3.Sum([z3.If(mine,1, 0) for mine in mine_neighbors])
        solver.add(z3.Implies(numberSpace[row][col] >= 0, numberSpace[row][col] == num_neighbors_w_mines))

print("On this board, _ marks a square definitely doesn't contain a mine")
print("\tand * marks a square that definitely contains a mine,")
print("\twhile a number tells you how many mines are adjacent to that square")

answer = "Ford the River"
while answer != "Q":
    # Current board
    print("\nCurrent Board:")
    for row in range(0, 5):
        for col in range(0, 5):
            if user_input[row][col] is not None:
                print(user_input[row][col], end=" ")
            elif provable(solver, hasMine[row][col]):
                print("*", end=" ")
            elif provable(solver, z3.Not(hasMine[row][col])):
                print("_", end=" ")
            # elif provable(solver, ): print("", end="")
            else:
                print("?", end=" ")
        print()

    print("You are exploring a grid of rows 0-4 and columns 0-4.")
    print("Please enter your board by typing in one of the following:")
    # Type in info about the number placements
    print("  2 0 1 if there are 2 mines adjacent to row 0 column 1")
    print("  Q if you have finished inputting the board and wish to see your solution or give up")

    # Find out what happened at this time step.
    answer = input("Please enter your board as (number of mines adjacent) (row) (column): ")
    # Adding user input into solve, overwriting the  numberSpaces
    if len(answer) == 5 and answer[0] in ["0", "1", "2", "3", "4", "5", "6", "7", "8"] and answer[1] == " " and answer [3] == " " and answer[2] in ["0", "1", "2", "3", "4"] and answer[4] in ["0", "1", "2", "3", "4"]:
        solver.add(numberSpace[int(answer[2])][int(answer[4])] == int(answer[0]))
        user_input[int(answer[2])][int(answer[4])] = int(answer[0])
    elif answer != "Q":
        print("Your response was not understood.")
    print()

# Print out final board
print("\nFinal Board:")
for row in range(0, 5):
    for col in range(0, 5):
        if user_input[row][col] is not None:
            print(user_input[row][col], end=" ")
        elif provable(solver, hasMine[row][col]):
            print("*", end=" ")
        elif provable(solver, z3.Not(hasMine[row][col])):
            print("_", end=" ")
        # elif provable(solver, ): print("", end="")
        else:
            print("?", end=" ")
    print()

