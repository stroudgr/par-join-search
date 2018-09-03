from terms import Term, Const, Var, term_types, comm_ops, assoc_ops, RSV, SV
from loop import Loop
from util import powerset
from solver import EqSolver
from rules import unflatten, flatten
from collections import Counter

import itertools

# =====================================================================
# Useful debug functions.
# =====================================================================

def printall(l):
    count = 1
    for x in l:
        print(count.__str__() +  ". ", x)
        count += 1

# =====================================================================
# Helper functions for the function generateStartTerms.
# =====================================================================

def rightAll(lp):
    """Returns a dictionary that maps right state variables to the correspoding
    'right' versions of the term.

    For example:
        0; s1 = s1 + a0
       -100; s2 = max(s2, s1+a0)
    Then the output is {sr1 : 0+a0, sr2 : max(-100, 0+a0)}"""

    # Dictionary which takes state variable s_i to the base case value of s_i.
    subst = lp.get_full_init_subst()
    # Function that takes term in loop and returns right induced version
    right = lambda term: term.apply_subst(subst)
    d = {}
    i = 1
    for term in lp.state_terms:
        rsv = RSV(i, lp.get_state_term(i-1).get_ret_type())
        d[rsv] = right(term)
        i += 1
    return d

def rightMe(term):
    """For the given term/invariant, returns the same invariant but with all of its
    state variables replaced with the RSV versions."""

    if type(term) == Const:
        return term
    if type(term) == Var:
        return term if term.vclass == "RSV" else RSV(term.index, term.type)
    return Term(term.op, [rightMe(x) for x in term.terms])

def removeDup(term):
    """Simplifies a term by removing any repeated subterms."""
    if type(term) in {Const, Var} or not term_types[term.op].fixed_args:
        return term
    term = Term(term.op, list(set(flatten(term).terms)))
    return term

def RSV_count(term):
    """Returns the number of occurences of a right state variable in a term."""

    if type(term) == Var and term.vclass == "RSV":
        return Counter({term: 1})
    if type(term) == Term:
        return sum([ Counter(RSV_count(subterm)) for subterm in term.terms], Counter())
    else:
        return Counter()

THRESHOLD = 1
def bounded_RSV_count(term):
    """Returns True iff a term has <= THRESHOLD number of occurences of a RSV in the term."""
    return all([y <= THRESHOLD for y in dict(RSV_count(term)).values()])


def highDepthRight(lp, solver, rights, init_term, ret, lastState):
    """Given the terms of rights are the form op(s_i,...) where s_i is the
    last state variable, this function takes all the terms in rights and adds
    sr_i to them, if it produces an equivalent term.

    For example, mss is the following:
        s1=0; s1=max(s1+a0,a0)
        s2=0; s2=max(s2,max(s1+a0,a0))
    The terms of rights initially should look like max(s2,...), and so this
    function makes sure they all look max(s2,sr2,...)."""

    # Conditions where this function should not be used.
    if type(init_term) in {Const, Var} or not term_types[init_term.op].fixed_args or lastState not in init_term.terms:
        return ret

    # init_term = op(s_i, ...) and new_term = op(s_i, sr_i, ...)
    new_term = init_term.__deepcopy__()
    n = lp.get_num_states()
    #rightSV = RSV(lastState.index, lastState.type)#rightMe(lastState)
    rightSV = RSV(n, lp.state_terms[n-1].get_ret_type())
    new_term.terms.append(rightSV)

    # Doesn't change output if adding right state variable doesn't produce an
    # equivalent term to original.
    if not equivalent(lp, solver, rights, init_term, new_term):
        return ret

    new_ret = []
    for item in ret:
        # True iff term is already of form op(s_i, sr_i,...)
        if type(item) == Term and rightSV in item.terms:
            new_ret.append(item)
        else:
            new_item = item.__deepcopy__()
            new_item.terms.append(rightSV)
            new_ret.append(new_item)
    return new_ret

# =====================================================================
# generateStartTerms:
# =====================================================================

def generateStartTerms(jsp):
    """Takes an JoinSearchProblem (jsp) and generates a potential list of better
    start terms for the search to start from."""
    lp = jsp.lp
    n = lp.get_num_states()
    solver = jsp.solver
    invars = jsp.invars
    init_term = flatten(lp.get_state_term(n - 1))

    #NOTE 1 unfold for problem like counting peaks
    # TODO add a check for these types of problems
    #init_term = flatten(init_term.apply_subst_multi(lp.get_full_state_subst(), 1))

    lastState = SV(n, init_term.get_ret_type())#Var("SV", "s", lp.get_num_states())

    # Dictionary mapping sr_i to 'right' version of the i'th term of the loop.
    rights = rightAll(lp)

    # Calls recursive helper.
    ret = generateStartTermsRecursive(init_term, init_term, solver, list(rights.keys()))

    # Filters the term to be only the ones that are equivalent to the original term of the program.
    ret = {x for x in ret if equivalent(lp, solver, rights, init_term, x)}

    ret = highDepthRight(lp, solver, rights, init_term, ret, lastState)

    # Removes terms with too many versions of the same right-state variables.
    ret = {term for term in ret if bounded_RSV_count(term)}

    # Removes repeat subterms in the each term.
    ret = {removeDup(x) for x in ret}

    print("init:", init_term)
    print("### Final output : ")
    printall(ret)
    print()
    return ret#.difference({init_term})

# =====================================================================
# Helpers for the function generateStartTermsRecursive.
# =====================================================================

def constantOnly(term):
    """Returns whether a term is made up of only constants and input variables or not."""
    if type(term) == Const:
        return True
    if type(term) == Var:
        return term.vclass != "SV"
    return all([constantOnly(subterm) for subterm in term.terms])

# =====================================================================
# generateStartTermsRecursive
# =====================================================================

def generateStartTermsRecursive(term, init_term, solver, rights):
    """Looks for constant only terms (in this term and the recursively returned subterms)
    and replaces them with the right terms. Will return the set of these generare terms
    that are equivalent to the original term."""


    if type(term) == Var and term.vclass == "SV":
        return [ term ]

    if type(term) in {Var, Const}:
        return [ term ] + [ right_term for right_term in rights if term.get_ret_type() == right_term.get_ret_type()  ]

    startTerms = list()
    # Generates all versions of this term, by replacing a subterm with a recursive call to generateStartTermsRecursive,
    # for every subterm.
    recursive = [generateStartTermsRecursive(subterm, init_term, solver, rights) for subterm in term.terms]

    for tup in itertools.product(*recursive):
        new_term = Term(term.op, [])
        new_term.terms = [x for x in tup]
        startTerms.append(new_term)

    if constantOnly(term):
        startTerms.extend([ right_term for right_term in rights if term.get_ret_type() == right_term.get_ret_type()  ])

    return startTerms

# =====================================================================
# Useful functions for generateStartTerms/generateStartTermsRecursive
#  and it's helpers
# =====================================================================

def equivalent(lp, solver, rights, orig, new, printMe=False):
    #assert(type(orig) in {Const, Term, Var} and type(new) in {Const, Term, Var})
    out = solver.equivalent(unflatten(flatten(orig)), unflatten(flatten(new.apply_subst(rights))))
    print("### Solver: ", flatten(orig), "v.s.", flatten(new), "(", flatten(new.apply_subst(rights)) , ") = ", out) if printMe else 0
    return out
