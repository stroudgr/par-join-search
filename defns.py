from terms import Const, Var, Term
from loop import Loop
from rules import *
from search import JoinSearchProblem
from parserr import parse


flattenRule = Rule(0, flatten)
unflattenRule = Rule(float('inf'), unflatten)
allUnflattenRule = Rule(float('inf'), all_unflatten)

zeroIntroduceRule = IdentIntroRule(40, '+', Const(0))
zeroElimRule = IdentElimRule(5, '+', Const(0))

andIntroduceRule = IdentIntroRule(40, '&', Const(True))
andElimRule = IdentElimRule(5, '&', Const(True))

orIntroduceRule = IdentIntroRule(40, '|', Const(False))
orElimRule = IdentElimRule(5, '|', Const(False))

boolIntroRule = InvIntroRule(60, '|', lambda x: x.negate(), Const(True), [Var('IV', 'a', 0, bool)])
boolElimRule = InvElimRule(5, '|', lambda x: x.negate(), Const(True))

andOR = DistInRule(20, ["|"], ["&"])

maxDistRule = DistInRule(20, ['+'], ['max'])
maxDistRevRule = DistOutRule(1, ['+'], ['max'])
maxIntroduceRule = DupIntroRule(60, 'max')
maxElimRule = DupElimRule(5, 'max')

bCondDistRule = DistInRule(20, ['&', '|'], ['BC'], [1,2])
bCondDistRevRule = DistOutRule(1, ['&', '|'], ['BC'], [1,2])
iCondDistRule = DistInRule(20, ['+', 'max'], ['IC'], [1,2])
iCondDistRevRule = DistOutRule(1, ['+', 'max'], ['IC'], [1,2])

# NOTE: this rule needs to know the variables of the problem.

s1 = Var("SV", "s", 1, bool)
s2 = Var("SV", "s", 2, bool)
a0 = Var("IV", "a", 0, bool)
boolAxioms = BooleanAxioms(40, [s1, s2, a0])

max_sum_rules = [maxDistRule, maxDistRevRule, maxIntroduceRule,
                 maxElimRule, zeroIntroduceRule, zeroElimRule]
just_max_rules = [maxIntroduceRule, maxElimRule]
bool_rules = [andIntroduceRule, andElimRule, #orIntroduceRule, orElimRule,
              iCondDistRule, iCondDistRevRule, boolIntroRule, boolElimRule,
              andOR, boolAxioms]
Os0s = [andElimRule,#boolIntroRule, boolElimRule,
              andOR,
              boolAxioms
              ]
              
cond_max_rules = max_sum_rules + bool_rules


def generate_max_invar_rules(invars):
    rules = []
    for invar in invars:
        rules.append(MaxStrengthenRule(60, invar))
        rules.append(MaxWeakenRule(60, invar))
    return rules
