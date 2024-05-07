# Python-Satisfiability-Solver
Python implementation of a satisfiability solver

## What is a Satisfiability (SAT) solver?

A SAT Solver is provided a boolean expression in the conjunctive normal form (CNF) aka Product of Sums 

e.g. (A + B + C) * (A' + D) * (B' + C' + E') ...

given the CNF, the SAT solver determines whether the expression is satisfiable or unsatisfiable. If satisfiable, an example combination of inputs that satisfies the expression is provided.

## How to Run?

From terminal, run:

python main.py tests/aim-50-1_6-yes1-1.cnf

to run the SAT solver on the CNF file provided.
