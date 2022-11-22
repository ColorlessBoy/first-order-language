import sys

sys.path.append(".")
sys.path.append("./src")

import unittest

from extprop import AndProp, ExistProp, IIFProp, OrProp
from proof import Assumption, Generalization, ModusPonens, Proof
from prop import ImplyProp, NotProp, VarProp
from theorem import (
    AndElim,
    AndExchange,
    AndIntro,
    Contradiction,
    Deduction,
    DoubleNotElim,
    DoubleNotIntro,
    ExistIntro,
    IIFElim,
    IIFExchange,
    IIFIntro,
    IIFToNotIIF,
    ImplyExchange,
    ImplyNotExchange,
    NotAndToOrNot,
    NotIIFToIIF,
    NotImplyExchange,
    NotImplyIntro,
    NotImplyToLeft,
    NotImplyToNotRight,
    NotOrToAndNot,
    NotToNotElim,
    NotToNotIntro,
    OrElim,
    OrExchange,
    OrIntro,
    Reflexive,
    Transitive,
)
from variable import Variable


class TheoremTest(unittest.TestCase):
    def test_Reflexive(self):
        """|=> a -> a."""
        vpa = VarProp(Variable("a"))
        p = ImplyProp(vpa, vpa)
        proof = Reflexive(vpa).proof
        self.assertEqual(proof, Proof(p))

    def test_Transitive(self):
        """{x = (a -> b), y = (b -> c)} |=> (a -> c)."""
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        vpc = VarProp(Variable("c"))

        proof_a2b = Proof(ImplyProp(vpa, vpb))
        proof_b2c = Proof(ImplyProp(vpb, vpc))
        proof_a2c = Proof(ImplyProp(vpa, vpc))

        proof = Transitive(proof_a2b, proof_b2c).proof
        self.assertEqual(proof, proof_a2c)

    def test_Deduction(self):
        """Deduction Theorem: {...T, Assume[a]} |=> b ===> {...T} |=> (a=>b)."""
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        assume1 = Assumption(vpa)
        assume2 = Assumption(ImplyProp(vpa, vpb))
        proof1 = ModusPonens(assume1, assume2)
        proof2 = Deduction(assume1, proof1).proof

        target = Proof(ImplyProp(assume1.prop, proof1.prop))

        self.assertEqual(proof2, target)

    def test_Deduction2(self):
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

    def test_ImplyExchange(self):
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        vpc = VarProp(Variable("c"))
        assume1 = Assumption(ImplyProp(vpa, ImplyProp(vpb, vpc)))
        assume2 = Assumption(ImplyProp(vpb, ImplyProp(vpa, vpc)))
        proof3 = ImplyExchange(assume1).proof
        self.assertEqual(assume2, proof3)

    def test_DoubleNotElim(self):
        vpa = VarProp(Variable("a"))
        assume1 = Assumption(ImplyProp(NotProp(NotProp(vpa)), vpa))
        theorem1 = DoubleNotElim(vpa)
        self.assertEqual(assume1, theorem1.proof)

    def test_DoubleNotIntro(self):
        vpa = VarProp(Variable("a"))
        assume1 = Assumption(ImplyProp(vpa, NotProp(NotProp(vpa))))
        theorem1 = DoubleNotIntro(vpa)
        self.assertEqual(assume1, theorem1.proof)

    def test_NotToNotElim(self):
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        assume1 = Assumption(
            ImplyProp(ImplyProp(NotProp(vpa), NotProp(vpb)), ImplyProp(vpb, vpa))
        )
        theorem1 = NotToNotElim(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_NotToNotIntro(self):
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        assume1 = Assumption(
            ImplyProp(ImplyProp(vpa, vpb), ImplyProp(NotProp(vpb), NotProp(vpa)))
        )
        theorem1 = NotToNotIntro(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_Contradiction(self):
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        assume1 = Assumption(
            ImplyProp(ImplyProp(vpa, vpb), ImplyProp(ImplyProp(NotProp(vpa), vpb), vpb))
        )
        theorem1 = Contradiction(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_ExistIntro(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop = ImplyProp(vpa, vpb)
        assume1 = Assumption(ImplyProp(ImplyProp(vpb, vpb), ExistProp(a, prop)))
        theorem1 = ExistIntro(prop, a, b)
        self.assertEqual(assume1, theorem1.proof)

    def test_NotImplyExchange(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop1 = ImplyProp(NotProp(vpa), vpb)
        prop2 = ImplyProp(NotProp(vpb), vpa)
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = NotImplyExchange(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_ImplyNotExchange(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop1 = ImplyProp(vpa, NotProp(vpb))
        prop2 = ImplyProp(vpb, NotProp(vpa))
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = ImplyNotExchange(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_NotImplyToLeft(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop1 = NotProp(ImplyProp(vpa, vpb))
        prop2 = ImplyProp(prop1, vpa)
        assume1 = Assumption(prop2)
        theorem1 = NotImplyToLeft(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_NotImplyToNotRight(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop1 = NotProp(ImplyProp(vpa, vpb))
        prop2 = ImplyProp(prop1, NotProp(vpb))
        assume1 = Assumption(prop2)
        theorem1 = NotImplyToNotRight(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_NotImplyIntro(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop1 = NotProp(ImplyProp(vpa, vpb))
        prop2 = ImplyProp(vpa, ImplyProp(NotProp(vpb), prop1))
        assume1 = Assumption(prop2)
        theorem1 = NotImplyIntro(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_AndElim(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop = AndProp(vpa, vpb)
        assume1 = Assumption(ImplyProp(prop, vpb))
        theorem1 = AndElim(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_AndIntro(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop = ImplyProp(vpa, ImplyProp(vpb, (AndProp(vpa, vpb))))
        assume1 = Assumption(prop)
        theorem1 = AndIntro(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_AndExchange(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop1 = AndProp(vpa, vpb)
        prop2 = AndProp(vpb, vpa)
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = AndExchange(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_OrElim(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop = ImplyProp(OrProp(vpa, vpb), ImplyProp(NotProp(vpa), vpb))
        assume1 = Assumption(prop)
        theorem1 = OrElim(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_OrIntro(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop = ImplyProp(vpb, OrProp(vpa, vpb))
        assume1 = Assumption(prop)
        theorem1 = OrIntro(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_OrExchange(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop = ImplyProp(OrProp(vpa, vpb), OrProp(vpb, vpa))
        assume1 = Assumption(prop)
        theorem1 = OrExchange(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_NotAndToOrNot(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop1 = NotProp(AndProp(vpa, vpb))
        prop2 = OrProp(NotProp(vpa), NotProp(vpb))
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = NotAndToOrNot(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_NotOrToAndNot(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop1 = NotProp(OrProp(vpa, vpb))
        prop2 = AndProp(NotProp(vpa), NotProp(vpb))
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = NotOrToAndNot(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_IIFElim(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop1 = IIFProp(vpa, vpb)
        prop2 = ImplyProp(vpa, vpb)
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = IIFElim(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_IIFIntro(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop1 = IIFProp(vpa, vpb)
        prop2 = ImplyProp(vpa, vpb)
        prop3 = ImplyProp(vpb, vpa)
        assume1 = Assumption(ImplyProp(prop2, ImplyProp(prop3, prop1)))
        theorem1 = IIFIntro(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_IIFExchange(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop1 = IIFProp(vpa, vpb)
        prop2 = IIFProp(vpb, vpa)
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = IIFExchange(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_IIFToNotIIF(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop1 = IIFProp(vpa, vpb)
        prop2 = IIFProp(NotProp(vpa), NotProp(vpb))
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = IIFToNotIIF(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_NotIIFToIIF(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop1 = IIFProp(vpa, vpb)
        prop2 = IIFProp(NotProp(vpa), NotProp(vpb))
        assume1 = Assumption(ImplyProp(prop2, prop1))
        theorem1 = NotIIFToIIF(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)
