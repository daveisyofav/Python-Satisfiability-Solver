######################################################################
# STRUCTURES: Main structures and functions used in DPLL process
######################################################################

# Constants for clause status and function results

CLAUSE_NORMAL = 100
CLAUSE_SAT = 101

CLAUSE_ONE_LEFT = 103
CLAUSE_CONFLICT = 104

SET_CAUSES_CONFLICT = 200
SET_NORMAL = 201

UNSET_CAUSES_UNRES = 300
UNSET_NORMAL = 301

# Make Maps function: Create dictionary structures watch_presence_map and dlis_wv

# watch_presence_map:
# Structure used to look up clauses that are watching a variable. This map will dynamically be updated when running
# the solver
# watch_presence_map: {1: literal1, 2: literal2, 3: literal3 ... }
# where literal1 is a Literal object for variable 1, which has attribute watch_presence: a list of clauses watching it
# watch_presence_map[3].watch_presence = [6, 7, 40, 42] means clauses 6, 7, 40, and 42 have 3 or -3 as a watch variable

# dlis_wv:
# Structure used to implement Dynamic Largest Individual Sum heuristic. dlis_wv maps positive and negative literals to
# a count of the number of UNRESOLVED clauses containing that literal. This structure will dynamically be updated when
# running solver


def make_maps(clause_list, num_vars):

    watch_presence = dict()
    dlis = dict()
    # Initialize watch_presence dictionary to contain literal objects
    # Initialize dlis_wv dictionary to contain zeros for positives and negatives of literals
    for literal_num in range(1, num_vars + 1):
        literal = Literal(literal_num)
        watch_presence[literal_num] = literal

        dlis[literal_num] = 0
        dlis[-1 * literal_num] = 0

    # Initialize watch presence of each literal to include all clauses watching it
    # Initialize dlis_wv of each literal to the number of clauses it occurs in
    for clause_index in range(len(clause_list)):
        clause = clause_list[clause_index]
        w1 = clause.watch1
        abs_w1 = abs(w1)

        watch_presence[abs_w1].add_watch_presence(clause_index)

        w2 = clause.watch2
        # W2 might be none if single literal clause
        if w2:
            abs_w2 = abs(w2)

            watch_presence[abs_w2].add_watch_presence(clause_index)

        for lit in clause.terms:
            dlis[lit] = dlis[lit] + 1

    return watch_presence, dlis


# Literal object: consists of an ID and an attribute watch_presence, which is a list of clauses currently watching this
# variable
class Literal:
    def __init__(self, _id):
        self.id = abs(_id)
        self.watch_presence = list()

    def add_watch_presence(self, clause_number):
        self.watch_presence.append(clause_number)

    def remove_watch_presence(self, clause_number):
        self.watch_presence.remove(clause_number)

    def get_watch_presence(self):
        return self.watch_presence


# Make clause list function: given a list of expressions (each expression a list of its literals), create list of
# clause objects
def make_clause_list(list_of_expressions):
    modified_list_of_expression = list()
    clause_list = list()
    for index in range(len(list_of_expressions)):
        skip = False
        expression = list_of_expressions[index]
        expression_set = set(expression)

        # Identify clauses to skip (contains a literal OR'd with its complement)
        for term in expression_set:
            # Check to see if a term and its complement are in the same clause
            complement = term * -1
            if complement in expression_set:
                # a + a' -> 1
                skip = True

        # If we skip this clause:
        # - do not add it to the list of expressions to pass to make_presence_map
        # - do not create a clause for it
        if skip:
            continue

        # Create a Clause-struct for this data
        clause = Clause(expression)
        modified_list_of_expression.append(expression)
        clause_list.append(clause)

    return modified_list_of_expression, clause_list


# Clause object: consists of its status, terms, and watch variables. Has methods for updating watch variables given
# the decision list (used when setting an assignment watched by the clause) and for checking SAT (used when unsetting
# an assignment watched by the clause during backtracking)
class Clause:
    def __init__(self, terms):
        # State
        self.satisfied = False

        self.terms = set(terms)
        self.terms_c = set([x * -1 for x in self.terms])
        self.num_terms = len(self.terms)

        self.watch1 = list(self.terms)[0]
        if len(terms) > 1:
            self.watch2 = list(self.terms)[1]
        else:
            self.watch2 = None

        # Previous watch for watch_presence updates in solver
        self.prev_watch1 = None
        self.prev_watch2 = None

        # Last literal for when clause has one literal left
        self.last_literal = None

    # Method for updating watch variables based on latest decisions list
    def watch_var_update(self, decisions_list, dlis):
        # Convert list to set for set methods
        decisions_set = set(decisions_list)

        # If there are clause terms that are satisfied, update DLIS and return CLAUSE_SAT
        sat_terms = self.terms.intersection(decisions_set)
        if sat_terms:
            dlis.update({x: dlis[x] - 1 for x in self.terms})
            self.satisfied = True

            return CLAUSE_SAT

        # UNRES terms are the complement of clause terms that have NOT been assigned by decisions
        unres_terms = self.terms_c.difference(decisions_set)
        num_unres_terms = len(unres_terms)

        # If all terms are UNSAT, we have a conflict
        if num_unres_terms == 0:
            return CLAUSE_CONFLICT

        # If there is only one left not UNSAT, we have one clause remaining
        elif num_unres_terms == 1:
            self.last_literal = unres_terms.pop() * -1  # Multiply by -1 bc using complements to find unres terms
            return CLAUSE_ONE_LEFT

        # Otherwise, we have multiple UNRES, we can choose two of our UNRES terms to be our watch variables
        # Multiply by -1 because currently unres_terms holds the complements of the clause literals
        else:
            self.prev_watch1 = self.watch1
            self.prev_watch2 = self.watch2
            self.watch1 = unres_terms.pop() * -1
            self.watch2 = unres_terms.pop() * -1

            return CLAUSE_NORMAL

    # Method for checking if the clause is still satisfied given the latest backtracked decisions list
    def check_sat(self, assignment, decisions_list, dlis):

        # Convert decisions list to set for set methods
        decisions_set = set(decisions_list)
        # Check if any of the clause terms are satisfied by the current decisions
        sat_terms = self.terms.intersection(decisions_set)

        # If after unsetting a watch variable, the clause is still SAT, update 1 watch variables to be a SAT term
        # this ensures that if we UNSAT this clause, we will see it and update our satisfied clause list
        # Make the other watch variable the term being UNSET
        if sat_terms:
            self.prev_watch1 = self.watch1
            self.prev_watch2 = self.watch2

            self.watch1 = sat_terms.pop()

            if assignment in self.terms:
                self.watch2 = assignment
            elif assignment in self.terms_c:
                self.watch2 = assignment * -1

            self.satisfied = True
            return UNSET_NORMAL

        # If unsetting makes this clause unresolved, update DLIS and return UNSET_CAUSES_UNRES
        else:
            dlis.update({x: dlis[x] + 1 for x in self.terms})
            self.satisfied = False
            return UNSET_CAUSES_UNRES
