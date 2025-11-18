# File: Wumpus.py
# Author: Chad Hogg
# An example of how Z3 can be used to answer questions about the Wumpus World.
# It only handles pits, not wumpuses.

# Necessary to use the Z3 library.
import z3

# Checks whether or not a statement can be proven, using proof-by-contradiction.
def provable(solver: z3.Solver, statement: z3.z3.BoolRef):
    # Start a new scope, so these changes aren't permanent.
    solver.push()
    # Assert the opposite of the thing we are trying to prove.
    solver.add(z3.Not(statement))
    # If there is no way to satisfy our rules, then the thing we are trying to prove must have been true.
    if(solver.check() == z3.unsat):
        solver.pop()
        return True
    else:
        solver.pop()
        return False

# Variables for various things that can be true.
visited = []
breezy = []
haspit = []
for row in range(0, 4):
    visited.append([])
    breezy.append([])
    haspit.append([])
    for col in range(0, 4):
        visited[row].append(z3.Bool("V" + str(row) + str(col)))
        breezy[row].append(z3.Bool("B" + str(row) + str(col)))
        haspit[row].append(z3.Bool("P" + str(row) + str(col)))

# Create a solver
solver = z3.Solver()

# Background knowledge about what breezes mean.
for row in range(0, 4):
    for col in range(0, 4):
        breezy_neighbors = []
        if row > 0: breezy_neighbors.append(haspit[row - 1][col])
        if row < 3: breezy_neighbors.append(haspit[row + 1][col])
        if col > 0: breezy_neighbors.append(haspit[row][col - 1])
        if col < 3: breezy_neighbors.append(haspit[row][col + 1])
        # If we have visited a place and not perceived a breeze, no pit is adjacent to it.
        solver.add(z3.Implies(z3.And(visited[row][col], z3.Not(breezy[row][col])),
                              z3.And([z3.Not(n) for n in breezy_neighbors])))
        # If we have perceived a breeze somewhere, a pit is adjacent to it.
        solver.add(z3.Implies(breezy[row][col],
                              z3.Or(breezy_neighbors)))

print("On this map, O marks a square that is definitely OK to step in")
print("\tand P marks a square that definitely contains a pit,")
print("\twhile B marks a square you have already stepped in where you felt a breeze,")
print("\tand V marks a square you stepped in with no breeze.")


# A big REPL
answer = "Blah"
while answer != "E":
    # Print out the things we can prove about pits.
    for row in range(3, -1, -1):
        for col in range(0, 4):
            if provable(solver, breezy[row][col]): print("B", end="")
            elif provable(solver, visited[row][col]): print("V", end="")
            elif provable(solver, haspit[row][col]): print("P", end="")
            elif provable(solver, z3.Not(haspit[row][col])): print("O", end="")
            else: print("?", end="")
        print()
    print()

    print("You are exploring a grid of rows 0-3 and columns 0-3.")
    print("Please type in one of the following:")
    print("\tV 2 3 if you visited row 2 column 3 and did not perceive a breeze there")
    print("\tB 0 2 if you visited row 0 column 2 and *did* feel a breeze there")
    print("\tE if you wish to exit because you won / died / got bored")

    # Find out what happened at this time step.
    answer = input("Your current experience: ")
    if len(answer) == 5 and answer[0] in ["V", "B"] and answer[1] == " " and answer[3] == " " and answer[2] in ["0", "1", "2", "3"] and answer[4] in ["0", "1", "2", "3"]:
        # Tell solver we visited this location.
        solver.add(visited[int(answer[2])][int(answer[4])])
        if answer[0] == "V":
            # And that we did not feel a breeze there.
            solver.add(z3.Not(breezy[int(answer[2])][int(answer[4])]))
        else:
            # And that we did feel a breeze there.
            assert(answer[0] == "B")
            solver.add(breezy[int(answer[2])][int(answer[4])])
    elif answer != "E":
        print("Your response was not understood.")

    print()

