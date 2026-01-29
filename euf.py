# Simple EUF solver
#
#

from math import floor, ceil
import argparse
import os
import sys
import functools

from utils import get_terms, split_equalities

from pysmt.typing import BOOL, REAL, INT, Type, FunctionType
from pysmt.shortcuts import (
    is_valid,
    Solver,
    Symbol, TRUE, FALSE, get_env,
    Real, Int,
    Not, And, Or, Implies, Iff,
    Equals, Function, NotEquals,
    get_atoms
)
from pysmt.logics import QF_LRA


class EGraph():
    """
    Graph used to compute the congruence closure
    """

    class ENode:
        """
        Node of the graph
        """

        def __init__(self, term, term_id, args):
            # Id of the
            self.id = term_id
            self.term = term
            # list of children nodes
            self.args = args
            # id for the equivalence class
            self.find = term_id
            # nodes for the parents
            self.eq_parents = set()

        def get_name(self):
            if (self.term.is_function_application()):
                return self.term.function_name()
            else:
                return self.term

        def __repr__(self):
            return "%d - %d - %s (%s) - [%s]" % (self.find, self.id,
                                                 self.get_name(), self.term,
                                                 ",".join([str(a) for a in self.args]))


    def __init__(self, terms):
        # Create the DAG from the list of terms
        raise NotImplementedError

    def node(self, node_id):
        """
        Returns the node with id equal to node_id
        """
        raise NotImplementedError

    def find(self, node_id):
        """
        Returns the representative of the equivalence class
        """
        raise NotImplementedError

    def union(self, id1, id2):
        """
        Returns the union of two equivalence classes.
        n2 becomes the representative of the class.
        """
        raise NotImplementedError

    def get_parents(self, node_id):
        """ Get the parents of all nodes in node_id congruence class """
        raise NotImplementedError

    def congruent(self, id1,id2):
        """
        Return true if id1 and id2 are congruent.
        """
        raise NotImplementedError

    def merge(self, id1, id2):
        """
        Merge the congruence class of id1 and id2
        """
        raise NotImplementedError()

    def merge_equalities(self, equalities):
        """
        Merge a list of equalities
        """
        raise NotImplementedError()

    def check_consistency(self, inequalities):
        """
        Check if any inequality in the list inequalities is not consistent

        Note: you need to merge all the equalities before calling this function
        """
        raise NotImplementedError()

    def print_graph(self):
        """ Print the nodes of the graph
        """
        for n in self.nodes:
            print(n)

    def print_eq_class(self, ostream = None):
        """ Prints the current equivalence class
        """

        if ostream is None:
            ostream = sys.stdout

        eq_class = {}
        for n in self.nodes:
            eq_set = set()
            if n.find in eq_class:
                eq_set = eq_class[n.find]
            else:
                eq_class[n.find] = eq_set
            eq_set.add(n)

        for (nodeid, nodes) in eq_class.items():
            ostream.write("{%s} " % ",".join([idn.term.serialize() for idn in nodes]))
        ostream.write("\n")


def euf_solver(formula):
    """
    Assume formula to be a conjunction of literals, and each literal has
    an equality as atom.
    The terms in the equalities should be function applications or "variables".

    Returns True if the formula is satisfiable and False otherwise.
    """

    # Gets a set of terms from formula
    terms = get_terms(formula)
    # Gets the equalities and inequalities of formula
    (equalities,inequalities) = split_equalities(formula)

    # HERE: construct the graph, compute the congruence closure, and check
    # if the terms in the inequalities end up in the same congruence class.

    print("WARNING: the euf_solver function is not implemented and always return UNSATISFIABLE!")

    return False


if __name__ == '__main__':
    main()
