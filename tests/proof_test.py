import sys

sys.path.append(".")
sys.path.append("./src")

import unittest

from proof import Proof, axiom1, axiom2, axiom3, axiom4, axiom5, gen, mp
from prop import ForallProp, ImplyProp, NotProp, VarProp
from variable import Variable


class ProofTest(unittest.TestCase):
    def test_reflexive(self):
        vpa = VarProp(Variable("a"))
        p = ImplyProp(vpa, vpa)

        proof1 = axiom1(vpa, vpa)
        proof2 = axiom1(vpa, p)
        proof3 = axiom2(vpa, p, vpa)
        proof4 = mp(proof2, proof3)
        proof5 = mp(proof1, proof4)

        self.assertEqual(proof5, Proof(p))
