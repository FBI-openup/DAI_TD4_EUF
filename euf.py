# Simple EUF solver
#Work of ZHANG Boyuan
#EUF solver + Lazy SMT
# all files structures on https://github.com/FBI-openup/DAI_TD4_EUF.git

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


def lazy_smt_solver(formula):
    """
    Lazy offline SMT solver for the Theory of Equality.
    
    This solver works by:
    1. Creating a boolean abstraction of the formula (map equality atoms to boolean variables)
    2. Enumerating boolean models using a SAT solver
    3. For each boolean model, convert it back to theory literals and check with euf_solver
    4. If a model is theory-consistent, return SAT
    5. If a model is theory-inconsistent, block it and try the next one
    6. If all models are exhausted, return UNSAT
    
    Args:
        formula: A PySMT formula (can contain boolean connectives and equality atoms)
        
    Returns:
        True if satisfiable, False otherwise
    """
    # Extract all equality atoms from the formula
    atoms = get_atoms(formula)
    
    # Create boolean abstraction: map each atom to a fresh boolean variable
    atom_to_bool = {}
    bool_to_atom = {}
    
    for i, atom in enumerate(atoms):
        bool_var = Symbol(f"b_{i}", BOOL)
        atom_to_bool[atom] = bool_var
        bool_to_atom[bool_var] = atom
    
    # Substitute atoms with boolean variables to get boolean abstraction
    bool_formula = formula.substitute(atom_to_bool)
    
    # Use a SAT solver to enumerate boolean models
    sat_solver = Solver(name="z3")
    sat_solver.add_assertion(bool_formula)
    
    # Try to find a satisfying assignment
    while sat_solver.solve():
        # Get the current model
        model = sat_solver.get_model()
        
        # Convert boolean model back to theory literals
        theory_literals = []
        for bool_var, atom in bool_to_atom.items():
            bool_value = model.get_value(bool_var)
            if bool_value.is_true():
                theory_literals.append(atom)
            else:
                theory_literals.append(Not(atom))
        
        # Create conjunction of theory literals
        if len(theory_literals) == 0:
            theory_formula = TRUE()
        elif len(theory_literals) == 1:
            theory_formula = theory_literals[0]
        else:
            theory_formula = And(theory_literals)
        
        # Check theory consistency with EUF solver
        is_theory_sat = euf_solver(theory_formula)
        
        if is_theory_sat:
            # Found a satisfying assignment
            return True
        else:
            # Block this model by adding the negation of the current assignment
            blocking_clause = []
            for bool_var, atom in bool_to_atom.items():
                bool_value = model.get_value(bool_var)
                if bool_value.is_true():
                    blocking_clause.append(Not(bool_var))
                else:
                    blocking_clause.append(bool_var)
            
            # Add blocking clause to prevent this assignment from being generated again
            if len(blocking_clause) > 0:
                sat_solver.add_assertion(Or(blocking_clause))
    
    # No satisfying assignment found
    return False


def main():
    """
    Main function for testing the solvers
    """
    # Example usage
    from pysmt.typing import Type
    
    # Create a simple test
    MySort = Type("MySort")
    a = Symbol("a", MySort)
    b = Symbol("b", MySort)
    c = Symbol("c", MySort)
    
    # Test 1: Simple satisfiable formula
    print("Test 1: a = b")
    formula1 = Equals(a, b)
    print(f"EUF Solver: {euf_solver(formula1)}")
    print(f"Lazy SMT Solver: {lazy_smt_solver(formula1)}")
    print()
    
    # Test 2: Simple unsatisfiable formula
    print("Test 2: a = b AND a != b")
    formula2 = And(Equals(a, b), Not(Equals(a, b)))
    print(f"EUF Solver: {euf_solver(formula2)}")
    print(f"Lazy SMT Solver: {lazy_smt_solver(formula2)}")
    print()
    
    # Test 3: Disjunction (only lazy SMT can handle directly)
    print("Test 3: (a = b) OR (b = c)")
    formula3 = Or(Equals(a, b), Equals(b, c))
    print(f"Lazy SMT Solver: {lazy_smt_solver(formula3)}")
    print()
    
    # Test 4: Complex formula with disjunction
    print("Test 4: ((a = b) OR (b = c)) AND (a != c)")
    formula4 = And(Or(Equals(a, b), Equals(b, c)), Not(Equals(a, c)))
    print(f"Lazy SMT Solver: {lazy_smt_solver(formula4)}")
    print()


if __name__ == '__main__':
    main()
