import sys

sys.path.append(".")
sys.path.append("./src")

import unittest

from extprop import AndProp, ExistProp
from proof import Assumption, Generalization, ModusPonens, Proof
from prop import ImplyProp, NotProp, VarProp
from theorem import (
    ConjunctionElimination,
    ConjunctionExchange,
    ConjunctionIntroduction,
    Contradiction,
    ContrapositiveElimination,
    ContrapositiveIntroduction,
    Deduction,
    Exchange,
    ExistentialRule,
    NegationElimination,
    NegationIntroduction,
    Reflexive,
    Transitive,
)
from variable import Variable


class TheoremTest(unittest.TestCase):
    def test_reflexive(self):
        """|=> a -> a."""
        vpa = VarProp(Variable("a"))
        p = ImplyProp(vpa, vpa)
        proof = Reflexive(vpa).proof
        self.assertEqual(proof, Proof(p))

    def test_transitive(self):
        """{x = (a -> b), y = (b -> c)} |=> (a -> c)."""
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        vpc = VarProp(Variable("c"))

        proof_a2b = Proof(ImplyProp(vpa, vpb))
        proof_b2c = Proof(ImplyProp(vpb, vpc))
        proof_a2c = Proof(ImplyProp(vpa, vpc))

        proof = Transitive(proof_a2b, proof_b2c).proof
        self.assertEqual(proof, proof_a2c)

    def test_deduction(self):
        """Deduction Theorem: {...T, Assume[a]} |=> b ===> {...T} |=> (a=>b)."""
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        assume1 = Assumption(vpa)
        assume2 = Assumption(ImplyProp(vpa, vpb))
        proof1 = ModusPonens(assume1, assume2)
        proof2 = Deduction(assume1, proof1).proof

        target = Proof(ImplyProp(assume1.prop, proof1.prop))

        self.assertEqual(proof2, target)

    def test_deduction2(self):
        """Deduction Theorem: {...T, Assume[a]} |=> b ===> {...T} |=> (a=>b)."""
        vpa = VarProp(Variable("a"))
        b = Variable("b")
        vpb = VarProp(b)
        assume1 = Assumption(vpa)
        assume2 = Assumption(ImplyProp(vpa, vpb))
        proof1 = ModusPonens(assume1, assume2)
        proof2 = Generalization(proof1, b)
        proof3 = Deduction(assume1, proof2).proof

        target = Proof(ImplyProp(assume1.prop, proof2.prop))

        self.assertEqual(proof3, target)

    def test_exchange(self):
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        vpc = VarProp(Variable("c"))
        assume1 = Assumption(ImplyProp(vpa, ImplyProp(vpb, vpc)))
        assume2 = Assumption(ImplyProp(vpb, ImplyProp(vpa, vpc)))
        proof3 = Exchange(assume1).proof
        self.assertEqual(assume2, proof3)

    def test_fromdoublenot(self):
        vpa = VarProp(Variable("a"))
        assume1 = Assumption(ImplyProp(NotProp(NotProp(vpa)), vpa))
        theorem1 = NegationElimination(vpa)
        self.assertEqual(assume1, theorem1.proof)

    def test_todoublenot(self):
        vpa = VarProp(Variable("a"))
        assume1 = Assumption(ImplyProp(vpa, NotProp(NotProp(vpa))))
        theorem1 = NegationIntroduction(vpa)
        self.assertEqual(assume1, theorem1.proof)

    def test_frominversenotnot(self):
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        assume1 = Assumption(
            ImplyProp(ImplyProp(NotProp(vpa), NotProp(vpb)), ImplyProp(vpb, vpa))
        )
        theorem1 = ContrapositiveElimination(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_toinversenotnot(self):
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        assume1 = Assumption(
            ImplyProp(ImplyProp(vpa, vpb), ImplyProp(NotProp(vpb), NotProp(vpa)))
        )
        theorem1 = ContrapositiveIntroduction(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_contradiction(self):
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        assume1 = Assumption(
            ImplyProp(ImplyProp(vpa, vpb), ImplyProp(ImplyProp(NotProp(vpa), vpb), vpb))
        )
        theorem1 = Contradiction(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_existentialrule(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop = ImplyProp(vpa, vpb)
        assume1 = Assumption(ImplyProp(ImplyProp(vpb, vpb), ExistProp(a, prop)))
        theorem1 = ExistentialRule(prop, a, b)
        self.assertEqual(assume1, theorem1.proof)

    def test_conjuctionelimination(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop = AndProp(vpa, vpb)
        assume1 = Assumption(ImplyProp(prop, vpb))
        theorem1 = ConjunctionElimination(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_conjuctionintroduction(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop = ImplyProp(vpa, ImplyProp(vpb, (AndProp(vpa, vpb))))
        assume1 = Assumption(prop)
        theorem1 = ConjunctionIntroduction(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_conjunctionexchange(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop1 = AndProp(vpa, vpb)
        prop2 = AndProp(vpb, vpa)
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = ConjunctionExchange(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)
