"""
Utility function to implement the euf-solver
"""


def get_terms(formula):
    """
    Assume formula to be a conjunction of literals, and each literal has
    an equality as atom.
    The terms in the equalities should be function applications or "variables".

    The function returns the set of terms of the formula.

    For example:
    f(a,b) = a and a = b and (not f(b) = a) would return the set:
    {a,b,f(a,b),f(b)}
    """

    terms = set()

    # Collect terms from equalities
    terms_to_visit = []
    for atom in formula.get_atoms():
        # Atoms here should be all equalities
        assert(atom.is_equals())
        lhr = atom.args()[0]
        rhs = atom.args()[1]
        terms_to_visit.append(lhr)
        terms_to_visit.append(rhs)

    # recursively visit terms (e.g., functions) and add new terms
    while len(terms_to_visit) > 0:
        term = terms_to_visit.pop()
        terms.add(term)
        if term.is_function_application():
            function_params = []
            function_name = term.function_name()
            for elem in term.args():
                function_params.append(elem)
            assert not function_name is None

            for t in function_params:
                if not t in terms:
                    terms_to_visit.append(t)
    return terms


def split_equalities(formula):
    """
    Assume formula to be a conjunction of literals, and each literal has
    an equality as atom.
    The terms in the equalities should be function applications or "variables".

    The function returns a pair (equalities, inequalities) where
    equalities/inequalities contains the list of *atoms* from the
    equalities/inequalities from the formula.

    Warning: the inequality list will still contains equalities, for example:
    f(a,b) = a and a = b and (not f(b) = a) would return:
    ([f(a,b) = a, a = b], [f(b) = a])
    """
    def split_equalities_rec(f, equalities, inequalities):
        if f.is_and():
            for a in f.args():
                split_equalities_rec(a, equalities, inequalities)
            return (equalities, inequalities)
        elif f.is_not():
            f1 = f.args()[0]
            assert(f1.is_equals())
            inequalities.append(f1)
            return (equalities, inequalities)
        elif f.is_equals():
            equalities.append(f)
            return (equalities, inequalities)
        else:
            raise Exception("Formula contains unknown node %s" % f)

    equalities = []
    inequalities = []
    return split_equalities_rec(formula, equalities, inequalities)
