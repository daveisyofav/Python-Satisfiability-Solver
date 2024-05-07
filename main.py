from dimacs import parse_dimacs
from output_format import output_format
from structures import make_maps, make_clause_list
from solver import DPLL

###########################################################################
# MAIN: Top level file for SAT Solver, calls functions to perform SAT Solve
###########################################################################

# Import Sys to access command line argument to get cnf file
import sys

# Optionally use tracemalloc to track memory usage:
# import tracemalloc
# tracemalloc.start()


# Get cnf file path from command line
cnf_file_name = sys.argv[1]

# Use parse_dimacs function to obtain cnf information from the cnf file
(list_of_expressions, numvars, numliterals) = parse_dimacs(cnf_file_name)

# Use make_clause_list function to obtain the clause_list
(modified_list_of_expressions, clause_list) = make_clause_list(list_of_expressions)

# Use make_maps function to obtain watch_presence_map and dlis_wv dictionaries (see wv_structures.py for structure details)
watch_presence_map, dlis = make_maps(clause_list, numvars)

# Instantiate a DPLL class from wv_solver.py with the cnf information obtained
solver = DPLL(watch_presence_map, clause_list, numvars, dlis)

# Call the solve method for our DPLL object
(solution, result) = solver.solve()

# Print results
output_format(solution, result, numvars)

# Optionally print the peak memory usage (must uncomment tracemalloc code above as well)
# curr, peak = tracemalloc.get_traced_memory()
# print(f"\nPEAK MEMORY: {peak}")
