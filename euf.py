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
        """
        Create the DAG from the list of terms
        """
        self.nodes = []
        self.term_to_id = {}  # Map from term to node ID
        
        def get_depth(term):
            """Calculate the depth/nesting level of a term"""
            if not term.is_function_application():
                return 0
            if len(list(term.args())) == 0:
                return 1
            return 1 + max(get_depth(arg) for arg in term.args())
        
        # Sort terms by depth (process shallower terms first)
        terms_list = list(terms)
        terms_list.sort(key=get_depth)
        
        # Create nodes for all terms
        for term in terms_list:
            if term not in self.term_to_id:
                # Get argument IDs if this is a function application
                arg_ids = []
                if term.is_function_application():
                    for arg in term.args():
                        if arg in self.term_to_id:
                            arg_ids.append(self.term_to_id[arg])
                        else:
                            # Create node for argument if not exists
                            arg_node_id = len(self.nodes)
                            arg_node = self.ENode(arg, arg_node_id, [])
                            self.nodes.append(arg_node)
                            self.term_to_id[arg] = arg_node_id
                            arg_ids.append(arg_node_id)
                
                # Create node for this term
                node_id = len(self.nodes)
                node = self.ENode(term, node_id, arg_ids)
                self.nodes.append(node)
                self.term_to_id[term] = node_id
                
                # Update parent references
                for arg_id in arg_ids:
                    self.nodes[arg_id].eq_parents.add(node_id)

    def node(self, node_id):
        """
        Returns the node with id equal to node_id
        """
        return self.nodes[node_id]

    def find(self, node_id):
        """
        Returns the representative of the equivalence class (with path compression)
        """
        node = self.nodes[node_id]
        if node.find != node_id:
            # Path compression
            node.find = self.find(node.find)
        return node.find

    def union(self, id1, id2):
        """
        Returns the union of two equivalence classes.
        id2 becomes the representative of the class.
        """
        root1 = self.find(id1)
        root2 = self.find(id2)
        
        if root1 != root2:
            # Make root2 the representative
            self.nodes[root1].find = root2

    def get_parents(self, node_id):
        """ Get the parents of all nodes in node_id congruence class """
        parents = set()
        # Find all nodes in the same equivalence class
        root = self.find(node_id)
        for node in self.nodes:
            if self.find(node.id) == root:
                parents.update(node.eq_parents)
        return parents

    def congruent(self, id1, id2):
        """
        Return true if id1 and id2 are congruent.
        Two nodes are congruent if:
        1. They have the same function symbol
        2. Their corresponding arguments are in the same equivalence classes
        """
        node1 = self.nodes[id1]
        node2 = self.nodes[id2]
        
        # Check if both are function applications
        if not (node1.term.is_function_application() and node2.term.is_function_application()):
            return False
        
        # Check if they have the same function name
        if node1.get_name() != node2.get_name():
            return False
        
        # Check if they have the same number of arguments
        if len(node1.args) != len(node2.args):
            return False
        
        # Check if corresponding arguments are in the same equivalence class
        for arg1_id, arg2_id in zip(node1.args, node2.args):
            if self.find(arg1_id) != self.find(arg2_id):
                return False
        
        return True

    def merge(self, id1, id2):
        """
        Merge the congruence class of id1 and id2
        """
        # If already in same class, nothing to do
        if self.find(id1) == self.find(id2):
            return
        
        # Get parents before merging
        parents1 = self.get_parents(id1)
        parents2 = self.get_parents(id2)
        
        # Merge the two equivalence classes
        self.union(id1, id2)
        
        # Combine all parents
        all_parents = parents1 | parents2
        
        # Check all pairs of parents for congruence
        parents_list = list(all_parents)
        for i in range(len(parents_list)):
            for j in range(i + 1, len(parents_list)):
                p1 = parents_list[i]
                p2 = parents_list[j]
                # If parents are congruent and not already in same class
                if self.find(p1) != self.find(p2) and self.congruent(p1, p2):
                    # Recursively merge congruent parents
                    self.merge(p1, p2)

    def merge_equalities(self, equalities):
        """
        Merge a list of equalities
        """
        for eq in equalities:
            # Get left and right sides of equality
            lhs = eq.args()[0]
            rhs = eq.args()[1]
            
            # Find node IDs
            if lhs in self.term_to_id and rhs in self.term_to_id:
                lhs_id = self.term_to_id[lhs]
                rhs_id = self.term_to_id[rhs]
                self.merge(lhs_id, rhs_id)

    def check_consistency(self, inequalities):
        """
        Check if any inequality in the list inequalities is not consistent

        Note: you need to merge all the equalities before calling this function
        """
        for ineq in inequalities:
            # Get left and right sides of inequality
            lhs = ineq.args()[0]
            rhs = ineq.args()[1]
            
            # Find node IDs
            if lhs in self.term_to_id and rhs in self.term_to_id:
                lhs_id = self.term_to_id[lhs]
                rhs_id = self.term_to_id[rhs]
                
                # If they are in the same equivalence class, we have a conflict
                if self.find(lhs_id) == self.find(rhs_id):
                    return False  # Inconsistent
        
        return True  # Consistent

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
    (equalities, inequalities) = split_equalities(formula)

    # Construct the graph
    graph = EGraph(terms)
    
    # Compute the congruence closure by merging all equalities
    graph.merge_equalities(equalities)
    
    # Check if the terms in the inequalities end up in the same congruence class
    is_consistent = graph.check_consistency(inequalities)

    return is_consistent


if __name__ == '__main__':
    main()
