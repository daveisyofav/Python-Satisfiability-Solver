def parse_dimacs(filename):
    # Parse the DIMACS format input to generate a list of clauses
    #
    # CREDIT: modified from https://stackoverflow.com/questions/28890268/parse-dimacs-cnf-file-python
    # Technically a new line doesn't have to mark the end of a clause, multiple clauses can be in one line
    cnf = list()
    cnf.append(list())
    maxvar = 0
    with open(filename, 'r') as file:
        for line in file:
            tokens = line.split()
            if len(tokens) != 0 and tokens[0] not in ("p", "c"):
                for token in tokens:
                    literal = int(token)
                    maxvar = max(maxvar, abs(literal))
                    if literal == 0:
                        cnf.append(list())
                    else:
                        cnf[-1].append(literal)

        assert len(cnf[-1]) == 0
        cnf.pop()
    return cnf, maxvar, len(cnf)
