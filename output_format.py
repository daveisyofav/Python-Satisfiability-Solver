def output_format(solution, result, numvars):
    final_format = dict()

    # Solution = None if result = UNSAT
    if solution:
        for i in solution:
            if i < 0:
                final_format[abs(i)] = 0
            else:  # i > 0
                final_format[abs(i)] = 1

    # 1/2 : Print SAT or UNSAT
    print(f"RESULT: {result}")

    # 2/2 : Print variable assignment
    if result == "SAT":
        print("ASSIGNMENT:", end="")
        for var in range(1, numvars + 1):
            if var in final_format:
                print(f" {var}={final_format[var]}", end="")
            else: # Print default case for variable assignment, 0
                print(f" {var}={0}", end="")

    return