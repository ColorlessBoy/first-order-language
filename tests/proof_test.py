import sys

sys.path.append(".")
sys.path.append("./src")

import unittest

from proof import Assumption, Axiom1, Axiom2, ModusPonens
from prop import ImplyProp, VarProp
from variable import Variable


class ProofTest(unittest.TestCase):
    def test_reflexive(self):
        vpa = VarProp(Variable("a"))
        p = ImplyProp(vpa, vpa)

        proof1 = Axiom1(vpa, vpa)
        proof2 = Axiom1(vpa, p)
        proof3 = Axiom2(vpa, p, vpa)
        proof4 = ModusPonens(proof2, proof3)
        proof5 = ModusPonens(proof1, proof4)

        self.assertEqual(proof5, Assumption(p))
