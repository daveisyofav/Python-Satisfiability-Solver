from structures import CLAUSE_NORMAL, CLAUSE_SAT, CLAUSE_ONE_LEFT, CLAUSE_CONFLICT
from structures import SET_NORMAL, SET_CAUSES_CONFLICT, UNSET_NORMAL, UNSET_CAUSES_UNRES

######################################################################
# SOLVER: Core DPLL solver algorithm using DPLL class
######################################################################

# Local constants for solver outputs, decision types, decision results, and forced decision results
SOLVED_SAT = "SAT"
SOLVED_UNSAT = "UNSAT"
SOLVED_ERROR = "ERROR"


DECISION_TYPE_FREE = 1001
DECISION_TYPE_BACKTRACK = 1002
DECISION_TYPE_FORCED = 1003

DECISION_CAUSES_CONFLICT = 1100
DECISION_CAUSES_SAT = 1101

FORCE_CAUSES_CONFLICT = 1200
FORCE_NORMAL = 1201

# The DPLL class hosts all attributes and methods for implementing the DPLL algorithm


class DPLL:
    def __init__(self, watch_presence_map, clause_list, numvars, dlis):
        self.watch_presence_map = watch_presence_map
        self.dlis = dlis
        self.clause_list = clause_list
        self.satisfied_clauses = set()
        self.forced_decision_queue = list()
        self.num_clauses = len(clause_list)

        self.free_decision_list = list()  # Keep track of free decisions for backtracking
        self.all_decisions_list = list()  # Keep track of free AND forced decisions for backtracking
        self.all_variables = set(range(1, numvars + 1))
        self.SATISFIED = False
        self.UNSATISFIABLE = False
        self.CONFLICT = False

    ###################################################################################
    # SOLVE FUNCTION: Makes initial free choice to set off full DPLL, returns results
    ###################################################################################
    def solve(self):

        # Run make_decision with a free choice
        # make_decision will recursively call itself to make further free decisions, forced decisions, and backtrack

        free_choice = self.choose_var_freely() * -1

        result = self.make_decision(free_choice)

        # Check if this DPLL has been determined to be UNSAT, or SAT
        if result == DECISION_CAUSES_SAT:
            return self.all_decisions_list, SOLVED_SAT

        elif result == DECISION_CAUSES_CONFLICT:
            return None, SOLVED_UNSAT

        else:
            return None, SOLVED_ERROR

    ###################################################################################
    # END OF SOLVE FUNCTION
    ###################################################################################

    ###################################################################################
    # BACKTRACKING FUNCTION - Backtrack to last free decision
    ###################################################################################

    def do_backtracking(self):
        # Change CONFLICT back to false
        self.CONFLICT = False

        # If there are no free decisions in the self.free_decision_list, that means the function is Unsatisfiable
        # We have already backtracked to all our free decisions and still found conflict
        if not self.free_decision_list:
            self.UNSATISFIABLE = True
            return 0

        # Get most recent free decision from self.free_decision_list
        last_free_decision = self.free_decision_list[-1]

        # Go through and UNSET the last free decision AND any forced decisions that occurred

        # To do so, find last_free_decision in the all_decisions_list and iterate from there
        free_decision_index = self.all_decisions_list.index(last_free_decision)
        end_index = len(self.all_decisions_list)
        for i in range(free_decision_index, end_index):
            # Unset variable in clauses
            self.unset(self.all_decisions_list[i], free_decision_index)

        # Remove all decisions from last free decision onward from all_decisions_list
        self.all_decisions_list = self.all_decisions_list[0:free_decision_index]

        # Remove that free decision from the free_decision_list, so we don't backtrack to the same place twice
        self.free_decision_list.pop()

        # Empty the forced_decision_queue as those forced decisions no longer need to be enforced
        self.forced_decision_queue.clear()

        return

    ###################################################################################
    # END OF BACKTRACKING FUNCTION
    ###################################################################################

    ###################################################################################
    # FORCE FUNCTION - Using BCP, make forced decisions
    ###################################################################################

    def do_forced_decisions(self):
        # If we have forced decisions in the forced_decision_queue that we haven't forced, then call a forced decision

        start = 0
        last_seen = len(self.forced_decision_queue)

        while last_seen - start > 0:
            last_seen = len(self.forced_decision_queue)
            # Get next literal to force ...
            next_forces = self.forced_decision_queue[start:last_seen]
            start = last_seen

            for force in next_forces:
                # If we are trying to set the complement of a previous choice, we must return: Bad path.
                if force * -1 in self.all_decisions_list:
                    return FORCE_CAUSES_CONFLICT

                if force not in self.all_decisions_list:
                    self.all_decisions_list.append(force)
                    set_result = self.set(force)

                    # Setting didn't work out, let's go back
                    if set_result == SET_CAUSES_CONFLICT:
                        return FORCE_CAUSES_CONFLICT

            # Update our pointer to try any subsequent forces
            last_seen = len(self.forced_decision_queue)

        # Remove entries from our queue, we've just set them
        if start > 0:
            del self.forced_decision_queue[0:]

        return FORCE_NORMAL

    ###################################################################################
    # END OF FORCE FUNCTION
    ###################################################################################

    ###################################################################################
    # MAKE DECISION FUNCTION - Given a free decision, set the variable and either call
    # backtracking, forced decisions, or recursively call make_decision until solved
    ###################################################################################

    def make_decision(self, provided_decision):

        # Try both versions of the decision
        complement_provided_decision = provided_decision * -1
        decisions = [provided_decision, complement_provided_decision]
        outcome = dict()

        for decision in decisions:
            # Add this decision to the free decision list ...
            self.free_decision_list.append(decision)
            self.all_decisions_list.append(decision)

            # Use set function to assign variable
            set_result = self.set(decision)

            if set_result == SET_CAUSES_CONFLICT:  # Setting the free choice didn't work out, try complement
                # Undo effects of making the last decision
                self.do_backtracking()

                # Try setting the complement, go to next loop iteration
                outcome[decision] = 0
                continue

            # After assigning variable, check if our function is satisfied ...
            if len(self.satisfied_clauses) == self.num_clauses:
                self.SATISFIED = True
                return DECISION_CAUSES_SAT

            # If not, decide what decision type our next decision will be: either free, forced, or backtrack
            # Then recursively call make_decision with that decision type
            else:

                # Go perform any forced decisions
                force_result = self.do_forced_decisions()

                if force_result == FORCE_CAUSES_CONFLICT:  # Setting the forced choices didn't work out, try complement
                    # Undo effects of making the last decision
                    self.do_backtracking()

                    # Try setting the complement, go to next loop iteration
                    outcome[decision] = 0
                    continue

                # Freely choose variable to assign and its polarity
                # If satisfied or none left, see 0 returned
                free_choice = self.choose_var_freely()

                if free_choice != 0:
                    # Recursively call make_decision
                    self.make_decision(free_choice)

                # After assigning variable, check if our function is satisfied ...
                if len(self.satisfied_clauses) == self.num_clauses:
                    self.SATISFIED = True
                    return DECISION_CAUSES_SAT

                # This decision didn't work. Undo and try complement
                self.do_backtracking()

                # Try setting the complement, go to next loop iteration
                outcome[decision] = 0
                continue

        return DECISION_CAUSES_CONFLICT

    ###################################################################################
    # END OF MAKE DECISION FUNCTION
    ###################################################################################

    ###################################################################################
    # CHOOSE FREELY FUNCTION - For free decisions, choose what variable to set
    ###################################################################################

    def choose_var_freely(self):
        # Choose a variable to assign and its polarity for a free decision

        # If satisfied, no free choices left to make
        if self.SATISFIED:
            return 0

        # Get a list of the unassigned literals
        assigned_vars = {abs(x) for x in self.all_decisions_list}
        unassigned_vars = self.all_variables.difference(assigned_vars)

        # Check if all variables are assigned, return 0 if so
        if len(unassigned_vars) == 0:
            return 0

        unassigned_opps = {-1 * x for x in unassigned_vars}
        all_unassigned = unassigned_vars.union(unassigned_opps)

        # Use unassigned literals to create a subdictionary of dlis_wv
        available_dlis = {k: self.dlis[k] for k in all_unassigned}

        # Get the key (literal) with the largest value (sum) from the available_dlis dictionary as our decision
        literal = max(available_dlis, key=available_dlis.get)

        # This literal is present in the most currently unresolved clauses
        return literal

    ###################################################################################
    # END OF CHOOSE FREELY FUNCTION
    ###################################################################################

    ###################################################################################
    # SET FUNCTION - Clauses watching the variable assigned will be checked for SAT,
    # unit clause, and conflict and will have watch variables updated as needed
    ###################################################################################

    def set(self, assignment):

        # Get literal from watch_presence_map
        literal = self.watch_presence_map[abs(assignment)]

        # Get watch_presence to see what clauses are watching this literal
        # Copy function required otherwise updates to watch presence changes our list iteration
        watch_presence = (literal.get_watch_presence()).copy()

        # Only iterate through clauses that have the assignment in its watch literals
        for index in watch_presence:

            # Only iterate through clauses that are not satisfied
            if index not in self.satisfied_clauses:

                # Get clause that is watching assignment
                clause = self.clause_list[index]

                # Try to update the watch variable. Result could be normal, one left, SAT, or conflict
                set_result = clause.watch_var_update(self.all_decisions_list, self.dlis)

                # No unit clause, conflict, or SAT: update watch variables
                if set_result == CLAUSE_NORMAL:
                    # Watch variables for this clause have been updated, update the watch_presence_map:

                    # Remove this clause from watch_presence_map's literals that no longer are watched by this clause
                    remove_var1 = abs(clause.prev_watch1)
                    remove_var2 = abs(clause.prev_watch2)
                    self.watch_presence_map[remove_var1].remove_watch_presence(index)
                    self.watch_presence_map[remove_var2].remove_watch_presence(index)

                    # Add this clause to watch_presence_map's literals that are newly watching this clause
                    new_var1 = abs(clause.watch1)
                    new_var2 = abs(clause.watch2)

                    self.watch_presence_map[new_var1].add_watch_presence(index)
                    self.watch_presence_map[new_var2].add_watch_presence(index)

                    continue

                # Unit clause: Add the remaining literal to the forced decision queue
                elif set_result == CLAUSE_ONE_LEFT:
                    remainder = clause.last_literal
                    complement = remainder * -1

                    if complement in self.all_decisions_list or complement in self.forced_decision_queue:
                        return SET_CAUSES_CONFLICT
                    self.forced_decision_queue.append(remainder)  # Get the single remaining literal
                    pass

                # SAT clause: add clause to satisfied clauses attribute
                elif set_result == CLAUSE_SAT:
                    self.satisfied_clauses.add(index)

                # Conflict in clause: Return SET_CAUSES_CONFLICT constant
                elif set_result == CLAUSE_CONFLICT:  # If assignment causes conflict, flag it with CONFLICT and return
                    self.CONFLICT = True
                    return SET_CAUSES_CONFLICT
        return SET_NORMAL

    ###################################################################################
    # END OF SET FUNCTION
    ###################################################################################

    ###################################################################################
    # UNSET FUNCTION - Check if clauses watching backtracked assignments are no longer
    # SAT and remove from SAT list
    ###################################################################################
    def unset(self, assignment, dec_list_end_index):
        # If a clause got satisfied by one of the decisions we are backtracking, that decision was one of that
        # clause's watch variables and the watch variable hasn't been updated, so watch_presence for the literal finds
        # the clauses of interest, then we only need to check the SAT clauses to see if they are now UNRES

        # Get literal from watch_presence_map
        literal = self.watch_presence_map[abs(assignment)]

        # Get clauses watching the literal
        # Copy function required otherwise updates to watch presence changes our list iteration
        watch_presence = (literal.get_watch_presence()).copy()

        # Iterate through clauses watching the literal
        for index in watch_presence:

            # Only iterate through satisfied clauses
            if index in self.satisfied_clauses:

                clause = self.clause_list[index]
                # check if the clause is still satisfied according to our updated decisions list
                check_sat_result = clause.check_sat(assignment, self.all_decisions_list[0:dec_list_end_index], self.dlis)

                # If clause is no longer SAT: remove from satisfied clause list
                if check_sat_result == UNSET_CAUSES_UNRES:
                    self.satisfied_clauses.remove(index)

                # if we UNSET a watch var of a clause, but it is still SAT, the clause updates a watch variable to
                # be one of its still SAT variables. That way we will be watching when a clause becomes UNRES
                else:
                    remove_var1 = abs(clause.prev_watch1)
                    remove_var2 = abs(clause.prev_watch2)
                    self.watch_presence_map[remove_var1].remove_watch_presence(index)
                    self.watch_presence_map[remove_var2].remove_watch_presence(index)
                    new_var1 = abs(clause.watch1)
                    new_var2 = abs(clause.watch2)
                    self.watch_presence_map[new_var1].add_watch_presence(index)
                    self.watch_presence_map[new_var2].add_watch_presence(index)

        return UNSET_NORMAL

    ###################################################################################
    # END OF UNSET FUNCTION
    ###################################################################################
