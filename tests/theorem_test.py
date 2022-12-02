import sys

sys.path.append(".")
sys.path.append("./src")

import unittest

from extprop import AndProp, ExistProp, IIFProp, OrProp
from proof import Assumption, Axiom1, ModusPonens, Proof
from prop import ForallProp, ImplyProp, NotProp, VarProp
from theorem import (
    AndElim,
    AndExchange,
    AndIntro,
    ChoiceToExist,
    Contradiction,
    Deduction,
    DoubleNotElim,
    DoubleNotIntro,
    ExistIntro,
    ExistRenameVar,
    ExistToExistExist,
    ForallAndToAndForall,
    ForallExchange,
    ForallIIFExchange,
    ForallImplyExist,
    ForallImplyToImplyExist,
    ForallImplyToImplyForall,
    ForallNotToForallNotIntro,
    ForallOrToOrForallExist,
    ForallXYToForallX,
    IIFDoubleNotElim,
    IIFDoubleNotIntro,
    IIFElim,
    IIFElimReverse,
    IIFExchange,
    IIFExistNotToNotForall,
    IIFFromEval,
    IIFIntro,
    IIFIntroFromProof,
    IIFReflexive,
    IIFToEval,
    IIFToNotIIF,
    IIFTransition,
    IIFTransitionFromProof,
    ImplyExchange,
    ImplyIIFExchange,
    ImplyNotExchange,
    NotAndToOrNot,
    NotExistToForallNot,
    NotForallToExistNot,
    NotFreeVarExistElim,
    NotFreeVarForallIntro,
    NotFreeVarImplyExistIIFForall,
    NotFreeVarImplyForallIIFForall,
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
    OrForallToForallOr,
    OrIntro,
    Reflexive,
    Replacement,
    ReplacementFromProof,
    TransitionWithEval,
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

    def test_TransitiveWithEval(self):
        """{x = (a -> b), y = (b -> c)} |=> (a -> c)."""
        x = Variable("x")
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        vpc = VarProp(Variable("c"))

        proof_a2b = Proof(ImplyProp(vpa, ExistProp(x, vpb)))
        proof_b2c = Proof(ImplyProp(NotProp(ForallProp(x, NotProp(vpb))), vpc))
        proof_a2c = Proof(ImplyProp(vpa, vpc))

        proof = TransitionWithEval(proof_a2b, proof_b2c).proof
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

    def test_IIFReflexive(self):
        vpa = VarProp(Variable("a"))
        assume1 = Assumption(IIFProp(vpa, vpa))
        theorem1 = IIFReflexive(vpa)
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

    def test_IIFTransition(self):
        a = Variable("a")
        b = Variable("b")
        c = Variable("c")
        vpa = VarProp(a)
        vpb = VarProp(b)
        vpc = VarProp(c)
        prop1 = IIFProp(vpa, vpb)
        prop2 = IIFProp(vpb, vpc)
        prop3 = IIFProp(vpa, vpc)
        assume1 = Assumption(ImplyProp(prop1, ImplyProp(prop2, prop3)))
        theorem1 = IIFTransition(vpa, vpb, vpc)
        self.assertEqual(assume1, theorem1.proof)

    def test_ForallExchange(self):
        x = Variable("x")
        y = Variable("y")
        vpa = VarProp(Variable("a"))
        prop1 = ForallProp(x, ForallProp(y, vpa))
        prop2 = ForallProp(y, ForallProp(x, vpa))
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = ForallExchange(vpa, x, y)
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

    def test_ForallXYToForallX(self):
        x = Variable("x")
        y = Variable("y")
        vpx = VarProp(x)
        vpy = VarProp(y)
        prop0 = ImplyProp(vpx, vpy)
        prop1 = ImplyProp(vpx, vpx)

        prop2 = ForallProp(x, ForallProp(y, prop0))
        prop3 = ForallProp(x, prop1)

        assume1 = Assumption(ImplyProp(prop2, prop3))
        theorem1 = ForallXYToForallX(prop0, x, y)
        self.assertEqual(assume1, theorem1.proof)

    def test_ForallImplyToImplyForall(self):
        x = Variable("x")
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))

        prop1 = ForallProp(x, ImplyProp(vpa, vpb))
        prop2 = ImplyProp(ForallProp(x, vpa), ForallProp(x, vpb))
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = ForallImplyToImplyForall(vpa, vpb, x)
        self.assertEqual(assume1, theorem1.proof)

    def test_ForallImplyToExistForall(self):
        x = Variable("x")
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))

        prop1 = ForallProp(x, ImplyProp(vpa, vpb))
        prop2 = ImplyProp(ExistProp(x, vpa), ExistProp(x, vpb))
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = ForallImplyToImplyExist(vpa, vpb, x)
        self.assertEqual(assume1, theorem1.proof)

    def test_ForallAndToAndForall(self):
        x = Variable("x")
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))

        prop1 = ForallProp(x, AndProp(vpa, vpb))
        prop2 = AndProp(ForallProp(x, vpa), ForallProp(x, vpb))
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = ForallAndToAndForall(vpa, vpb, x)
        self.assertEqual(assume1, theorem1.proof)

    def test_NotForallToExistNot(self):
        x = Variable("x")
        vpa = VarProp(Variable("a"))

        prop1 = NotProp(ForallProp(x, vpa))
        prop2 = ExistProp(x, NotProp(vpa))
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = NotForallToExistNot(vpa, x)
        self.assertEqual(assume1, theorem1.proof)

    def test_OrForallToForallOr(self):
        x = Variable("x")
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))

        prop1 = OrProp(ForallProp(x, vpa), ForallProp(x, vpb))
        prop2 = ForallProp(x, OrProp(vpa, vpb))
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = OrForallToForallOr(vpa, vpb, x)
        self.assertEqual(assume1, theorem1.proof)

    def test_ForallOrToOrForallExist(self):
        x = Variable("x")
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))

        prop1 = ForallProp(x, OrProp(vpa, vpb))
        prop2 = OrProp(ForallProp(x, vpa), ExistProp(x, vpb))
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = ForallOrToOrForallExist(vpa, vpb, x)
        self.assertEqual(assume1, theorem1.proof)

    def test_ForallNotToForallNotIntro(self):
        x = Variable("x")
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))

        prop1 = ForallProp(x, ImplyProp(vpa, vpb))
        prop2 = ImplyProp(ForallProp(x, NotProp(vpb)), ForallProp(x, NotProp(vpa)))
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = ForallNotToForallNotIntro(vpa, vpb, x)
        self.assertEqual(assume1, theorem1.proof)

    def test_ForallImplyExist(self):
        x = Variable("x")
        y = Variable("y")
        vpa = VarProp(Variable("a"))
        vpx = VarProp(x)
        vpy = VarProp(y)
        prop1 = ImplyProp(vpa, ImplyProp(vpx, vpy))
        prop2 = ImplyProp(vpa, ImplyProp(vpx, vpx))
        prop3 = ForallProp(x, ImplyProp(prop2, ExistProp(y, prop1)))
        assume1 = Assumption(prop3)
        theorem1 = ForallImplyExist(prop1, x, y)
        self.assertEqual(assume1, theorem1.proof)

    def test_NotExistToForallNot(self):
        x = Variable("x")
        vpa = VarProp(Variable("a"))
        prop1 = NotProp(ExistProp(x, vpa))
        prop2 = ForallProp(x, NotProp(vpa))
        prop3 = ImplyProp(prop1, prop2)
        assume1 = Assumption(prop3)
        theorem1 = NotExistToForallNot(vpa, x)
        self.assertEqual(assume1, theorem1.proof)

    def test_ExistToExistExist(self):
        x = Variable("x")
        y = Variable("y")
        vpx = VarProp(x)
        vpy = VarProp(y)
        vpa = VarProp(Variable("a"))
        prop1 = ImplyProp(vpa, ImplyProp(vpx, vpx))
        prop2 = ImplyProp(vpa, ImplyProp(vpx, vpy))

        prop3 = ExistProp(x, prop1)
        prop4 = ExistProp(x, ExistProp(y, prop2))
        prop5 = ImplyProp(prop3, prop4)
        assume1 = Assumption(prop5)
        theorem1 = ExistToExistExist(prop2, x, y)
        self.assertEqual(assume1, theorem1.proof)

    def test_NotFreeVarForallIntro(self):
        vpa = VarProp(Variable("a"))
        x = Variable("x")
        assume1 = Assumption(ImplyProp(vpa, ForallProp(x, vpa)))
        theorem1 = NotFreeVarForallIntro(vpa, x)
        self.assertEqual(assume1, theorem1.proof)

    def test_NotFreeVarExistElim(self):
        vpa = VarProp(Variable("a"))
        x = Variable("x")
        assume1 = Assumption(ImplyProp(ExistProp(x, vpa), vpa))
        theorem1 = NotFreeVarExistElim(vpa, x)
        self.assertEqual(assume1, theorem1.proof)

    def test_NotFreeVarImplyForallIIFForall(self):
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        x = Variable("x")
        prop1 = ImplyProp(vpa, ForallProp(x, vpb))
        prop2 = ForallProp(x, ImplyProp(vpa, vpb))
        assume1 = Assumption(IIFProp(prop1, prop2))
        theorem1 = NotFreeVarImplyForallIIFForall(vpa, vpb, x)
        self.assertEqual(assume1, theorem1.proof)

    def test_NotFreeVarImplyExistIIFForall(self):
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        x = Variable("x")
        prop1 = ImplyProp(ExistProp(x, vpb), vpa)
        prop2 = ForallProp(x, ImplyProp(vpb, vpa))
        assume1 = Assumption(IIFProp(prop1, prop2))
        theorem1 = NotFreeVarImplyExistIIFForall(vpa, vpb, x)
        self.assertEqual(assume1, theorem1.proof)

    def test_ForallIIFExchange(self):
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        x = Variable("x")
        prop1 = ForallProp(x, IIFProp(vpa, vpb))
        prop2 = IIFProp(ForallProp(x, vpa), ForallProp(x, vpb))
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = ForallIIFExchange(vpa, vpb, x)
        self.assertEqual(assume1, theorem1.proof)

    def test_ImplyIIFExchange(self):
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        vpc = VarProp(Variable("c"))
        vpd = VarProp(Variable("d"))
        prop1 = IIFProp(vpa, vpb)
        prop2 = IIFProp(vpc, vpd)
        prop3 = IIFProp(ImplyProp(vpa, vpc), ImplyProp(vpb, vpd))
        prop4 = ImplyProp(prop1, ImplyProp(prop2, prop3))
        assume1 = Assumption(prop4)
        theorem1 = ImplyIIFExchange(vpa, vpb, vpc, vpd)
        self.assertEqual(assume1, theorem1.proof)

    def test_Replacement1(self):
        a = Variable("a")
        b = Variable("b")
        x = Variable("x")
        p1 = VarProp(a)
        p2 = VarProp(b)
        p3 = NotProp(ImplyProp(VarProp(x), ImplyProp(p1, p2)))
        p4 = NotProp(ImplyProp(VarProp(x), ImplyProp(p2, p2)))

        prop1 = ForallProp(b, ForallProp(a, IIFProp(p1, p2)))
        prop2 = IIFProp(p3, p4)
        prop3 = ImplyProp(prop1, prop2)
        assume1 = Assumption(prop3)

        prop1 = ForallProp(a, ForallProp(b, IIFProp(p1, p2)))
        prop2 = IIFProp(p3, p4)
        prop3 = ImplyProp(prop1, prop2)
        assume2 = Assumption(prop3)

        theorem1 = Replacement(p1, p2, p3)
        self.assertTrue(assume1 == theorem1.proof or assume2 == theorem1.proof)

    def test_Replacement2(self):
        a = Variable("a")
        b = Variable("b")
        x = Variable("x")
        p1 = VarProp(a)
        p2 = VarProp(b)
        p3 = ImplyProp(VarProp(x), ImplyProp(p1, p2))
        p4 = ImplyProp(VarProp(x), ImplyProp(p2, p2))

        prop1 = ForallProp(b, ForallProp(a, IIFProp(p1, p2)))
        prop2 = IIFProp(p3, p4)
        prop3 = ImplyProp(prop1, prop2)
        assume1 = Assumption(prop3)

        prop1 = ForallProp(a, ForallProp(b, IIFProp(p1, p2)))
        prop2 = IIFProp(p3, p4)
        prop3 = ImplyProp(prop1, prop2)
        assume2 = Assumption(prop3)

        theorem1 = Replacement(p1, p2, p3)
        self.assertTrue(assume1 == theorem1.proof or assume2 == theorem1.proof)

    def test_Replacement3(self):
        a = Variable("a")
        b = Variable("b")
        x = Variable("x")
        p1 = VarProp(a)
        p2 = VarProp(b)
        p3 = ForallProp(x, ImplyProp(p1, p2))
        p4 = ForallProp(x, ImplyProp(p2, p2))

        prop1 = ForallProp(a, ForallProp(b, IIFProp(p1, p2)))
        prop2 = IIFProp(p3, p4)
        prop3 = ImplyProp(prop1, prop2)
        assume1 = Assumption(prop3)

        prop1 = ForallProp(b, ForallProp(a, IIFProp(p1, p2)))
        prop2 = IIFProp(p3, p4)
        prop3 = ImplyProp(prop1, prop2)
        assume2 = Assumption(prop3)

        theorem1 = Replacement(p1, p2, p3)
        self.assertTrue(assume1 == theorem1.proof or assume2 == theorem1.proof)

    def test_Replacement4(self):
        a = Variable("a")
        b = Variable("b")
        x = Variable("x")
        vpa = VarProp(a)
        vpb = VarProp(b)
        vpx = VarProp(x)
        p3 = AndProp(vpx, ImplyProp(vpa, vpb))
        p4 = AndProp(vpx, ImplyProp(vpb, vpb))

        prop1 = ForallProp(a, ForallProp(b, IIFProp(vpa, vpb)))
        prop2 = IIFProp(p3, p4)
        prop3 = ImplyProp(prop1, prop2)
        assume1 = Assumption(prop3)

        prop1 = ForallProp(b, ForallProp(a, IIFProp(vpa, vpb)))
        prop2 = IIFProp(p3, p4)
        prop3 = ImplyProp(prop1, prop2)
        assume2 = Assumption(prop3)

        theorem1 = Replacement(vpa, vpb, p3)
        self.assertTrue(assume1 == theorem1.proof or assume2 == theorem1.proof)

    def test_Replacement5(self):
        a = Variable("a")
        b = Variable("b")
        x = Variable("x")
        vpa = VarProp(a)
        vpb = VarProp(b)
        vpx = VarProp(x)
        p3 = OrProp(vpx, ImplyProp(vpa, vpb))
        p4 = OrProp(vpx, ImplyProp(vpb, vpb))

        prop1 = ForallProp(a, ForallProp(b, IIFProp(vpa, vpb)))
        prop2 = IIFProp(p3, p4)
        prop3 = ImplyProp(prop1, prop2)
        assume1 = Assumption(prop3)

        prop1 = ForallProp(b, ForallProp(a, IIFProp(vpa, vpb)))
        prop2 = IIFProp(p3, p4)
        prop3 = ImplyProp(prop1, prop2)
        assume2 = Assumption(prop3)

        theorem1 = Replacement(vpa, vpb, p3)
        self.assertTrue(assume1 == theorem1.proof or assume2 == theorem1.proof)

    def test_Replacement6(self):
        a = Variable("a")
        b = Variable("b")
        x = Variable("x")
        vpa = VarProp(a)
        vpb = VarProp(b)
        vpx = VarProp(x)
        p3 = IIFProp(vpx, ImplyProp(vpa, vpb))
        p4 = IIFProp(vpx, ImplyProp(vpb, vpb))

        prop1 = ForallProp(a, ForallProp(b, IIFProp(vpa, vpb)))
        prop2 = IIFProp(p3, p4)
        prop3 = ImplyProp(prop1, prop2)
        assume1 = Assumption(prop3)

        prop1 = ForallProp(b, ForallProp(a, IIFProp(vpa, vpb)))
        prop2 = IIFProp(p3, p4)
        prop3 = ImplyProp(prop1, prop2)
        assume2 = Assumption(prop3)

        theorem1 = Replacement(vpa, vpb, p3)
        self.assertTrue(assume1 == theorem1.proof or assume2 == theorem1.proof)

    def test_Replacement7(self):
        a = Variable("a")
        b = Variable("b")
        x = Variable("x")
        vpa = VarProp(a)
        vpb = VarProp(b)
        p3 = ExistProp(x, ImplyProp(vpa, vpb))
        p4 = ExistProp(x, ImplyProp(vpb, vpb))

        prop1 = ForallProp(a, ForallProp(b, IIFProp(vpa, vpb)))
        prop2 = IIFProp(p3, p4)
        prop3 = ImplyProp(prop1, prop2)
        assume1 = Assumption(prop3)

        prop1 = ForallProp(b, ForallProp(a, IIFProp(vpa, vpb)))
        prop2 = IIFProp(p3, p4)
        prop3 = ImplyProp(prop1, prop2)
        assume2 = Assumption(prop3)

        theorem1 = Replacement(vpa, vpb, p3)
        self.assertTrue(assume1 == theorem1.proof or assume2 == theorem1.proof)

    def test_ReplacementFromProof(self):
        a = Variable("a")
        b = Variable("b")
        x = Variable("x")
        p1 = VarProp(a)
        p2 = VarProp(b)
        p3 = NotProp(ImplyProp(VarProp(x), ImplyProp(p1, p2)))
        p4 = NotProp(ImplyProp(VarProp(x), ImplyProp(p2, p2)))

        prop2 = IIFProp(p3, p4)
        assume1 = Assumption(prop2)

        proof1 = Proof(IIFProp(p1, p2))
        theorem1 = ReplacementFromProof(proof1, p3)
        self.assertTrue(assume1 == theorem1.proof)

    def test_IIFToEval(self):
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        prop1 = AndProp(vpa, vpb)
        assume1 = Assumption(IIFProp(prop1, prop1.eval()))
        theorem1 = IIFToEval(prop1)
        self.assertEqual(assume1, theorem1.proof)

    def test_IIFFromEval(self):
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        prop1 = AndProp(vpa, vpb)
        assume1 = Assumption(IIFProp(prop1.eval(), prop1))
        theorem1 = IIFFromEval(prop1)
        self.assertEqual(assume1, theorem1.proof)

    def test_IIFElimReverse(self):
        a = Variable("a")
        b = Variable("b")
        vpa = VarProp(a)
        vpb = VarProp(b)
        prop1 = IIFProp(vpa, vpb)
        prop2 = ImplyProp(vpb, vpa)
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = IIFElimReverse(vpa, vpb)
        self.assertEqual(assume1, theorem1.proof)

    def test_IIFIntroFromProof(self):
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        prop1 = ImplyProp(vpa, vpb)
        prop2 = ImplyProp(vpb, vpa)
        prop3 = IIFProp(vpa, vpb)
        assume1 = Assumption(prop3)
        proof1 = Proof(prop1)
        proof2 = Proof(prop2)
        theorem1 = IIFIntroFromProof(proof1, proof2)
        self.assertEqual(assume1, theorem1.proof)

    def test_IIFTransitionFromProof(self):
        vpa = VarProp(Variable("a"))
        vpb = VarProp(Variable("b"))
        vpc = VarProp(Variable("c"))
        proof1 = Proof(IIFProp(vpa, vpb))
        proof2 = Proof(IIFProp(vpb, vpc))
        assume1 = Assumption(IIFProp(vpa, vpc))
        theorem1 = IIFTransitionFromProof(proof1, proof2)
        self.assertEqual(assume1, theorem1.proof)

    def test_IIFDoubleNotElim(self):
        vpa = VarProp(Variable("a"))
        assume1 = Assumption(IIFProp(NotProp(NotProp(vpa)), vpa))
        theorem1 = IIFDoubleNotElim(vpa)
        self.assertEqual(assume1, theorem1.proof)

    def test_IIFDoubleNotIntro(self):
        vpa = VarProp(Variable("a"))
        assume1 = Assumption(IIFProp(vpa, NotProp(NotProp(vpa))))
        theorem1 = IIFDoubleNotIntro(vpa)
        self.assertEqual(assume1, theorem1.proof)

    def test_IIFExistNotToNotForall(self):
        x = Variable("x")
        vpa = VarProp(Variable("a"))
        prop1 = ExistProp(x, NotProp(vpa))
        prop2 = NotProp(ForallProp(x, vpa))
        assume1 = Assumption(IIFProp(prop1, prop2))
        theorem1 = IIFExistNotToNotForall(vpa, x)
        self.assertEqual(assume1, theorem1.proof)

    def test_ExistRenameVar(self):
        x = Variable("x")
        y = Variable("y")
        vpx = VarProp(x)
        vpy = VarProp(y)
        vpa = VarProp(Variable("a"))
        prop1 = ExistProp(x, ImplyProp(vpa, vpx))
        prop2 = ExistProp(y, ImplyProp(vpa, vpy))
        assume1 = Assumption(ImplyProp(prop1, prop2))
        theorem1 = ExistRenameVar(ImplyProp(vpa, vpx), x, y)
        self.assertEqual(assume1, theorem1.proof)

    def test_ChoiceToExist(self):
        x = Variable("x")
        vpx = VarProp(x)
        vpa = VarProp(Variable("a"))
        assumeX = Assumption(vpx)
        proof1 = ModusPonens(assumeX, Axiom1(vpx, vpa))  # assume(x) |=> vpa => vpx
        prop2 = ImplyProp(
            ExistProp(x, vpx), ExistProp(x, ImplyProp(vpa, vpx))
        )  # (exists x, x) => (exists x, a => x)
        assume1 = Assumption(prop2)
        theorem1 = ChoiceToExist(proof1, vpx, x)
        self.assertEqual(assume1, theorem1.proof)
