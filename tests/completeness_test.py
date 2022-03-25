#!/usr/bin/env python
import sys
sys.path.append('.')
sys.path.append('./src')
import unittest
from atom import *
from folatom import *
from follemma import *
from completeness import complete

class CompletenessTest(unittest.TestCase):

    def test_completeness(self):
        a = get_atom('a')
        b = get_atom('b')
        c = axiom1(a, b).getAtom()

        s = complete(c)
        self.assertEqual(str(s), 'Complete{h_imply(a, h_imply(b, a))}')
        self.assertEqual(str(s.getAtom()), 'h_imply(a, h_imply(b, a))')

