""" Test the transition system """

import logging
import os
import sys
import argparse

from pysmt.typing import BOOL
from pysmt.shortcuts import Symbol, TRUE, FALSE, get_env, GE, Real
from pysmt.shortcuts import Not, And, Or, Implies, Iff, ExactlyOne
from pysmt.shortcuts import is_valid, is_sat, reset_env, Solver
from pysmt.exceptions import SolverAPINotFound
from pysmt.smtlib.parser.parser import SmtLibParser

from euf import euf_solver

def get_solver():
    return Solver(name="z3")

def _read_formula(solver, f):
    parser = SmtLibParser()
    script = parser.get_script(f)

    formula = script.get_last_formula()

    last_command = script.commands.pop()

    script.evaluate(solver)

    return formula


def test_file(input_file):
    env = reset_env()
    solver = get_solver()
    with open(input_file) as f:
        formula = _read_formula(solver, f)

        is_sat = euf_solver(formula)
        is_sat_correct = solver.solve()

        def strres(res):
            return "Satisfiable" if res else "Unsatisfiable"

        if (is_sat != is_sat_correct):
            print("[FAILED] %s: you returned %s instead of %s" % (os.path.basename(input_file),
                                                         strres(is_sat),
                                                         strres(is_sat_correct)))
            return False
        else:
            print("[SUCCESS] %s: returned %s" % (os.path.basename(input_file),
                                                     strres(is_sat)))
            return True

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("-t", "--test_case", help="Run a specific test case")
    args = parser.parse_args()


    current_path = os.path.dirname(os.path.abspath(__file__))
    input_path = os.path.join(current_path, "test_cases")
    test_cases = []
    for f in os.listdir(input_path):
        test_cases.append(f)
    test_cases.sort()

    test_case = None
    if not args.test_case is None:
        test_case = args.test_case
        if not test_case in test_cases:
            print("Test case %s not found in %s" % (test_case, input_path))
            return 1
        test_cases = [test_case]

    failed = False
    print("Runing test cases:")
    for f in test_cases:

        if not f.endswith(".smt2"):
            continue

        input_file = os.path.join(input_path, f)
        correct = test_file(input_file)
        failed = failed or (not correct)
    if failed:
        return 1

    return 0

if __name__ == '__main__':
    ret = main()
    sys.exit(ret)

