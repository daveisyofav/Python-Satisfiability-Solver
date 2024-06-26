# 2024 - Python-Satisfiability-Solver
Python implementation of a satisfiability solver

Developed in ECE 51216 Digital Design Automation

## What is a Satisfiability (SAT) solver?

A SAT Solver is provided a boolean expression in the conjunctive normal form (CNF) aka Product of Sums 

e.g. (A + B + C) * (A' + D) * (B' + C' + E') ...

given the CNF, the SAT solver determines whether the expression is satisfiable or unsatisfiable. If satisfiable, an example combination of inputs that satisfies the expression is provided.

## How to Run?

From terminal, run:

python main.py tests/aim-50-1_6-yes1-1.cnf

to run the SAT solver on the CNF file provided.

## File Contents
main.py - Top level calls lower functions

solver - Implements backtracking algorithm with watch variables and dynamic largest individual sum (DLIS) heuristics

structures - Define classes and functions used in solver

dimacs - parse the input CNF file into a clause list

output_format - format print statement
