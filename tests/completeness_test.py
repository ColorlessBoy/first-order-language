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
        c = h_imply(a, b)

        s = complete(c)
        assumptions = getassume(s)

        self.assertEqual(str(s), 'Complete{h_imply(a, b)}')
        self.assertEqual(str(s.getAtom()), 'h_imply(a, b)')
        self.assertEqual(str(assumptions[0]), 'h_imply(h_imply(a, h_not(b)), h_imply(a, b))')


