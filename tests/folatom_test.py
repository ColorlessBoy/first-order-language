import sys
sys.path.append('.')
sys.path.append('./src')

import unittest
from atom import get_atom, h_imply
from folatom import axiom1, axiom2, axiom3, modus_ponens as mp, assume

class FolAtomTest(unittest.TestCase):

    def test_axiom1(self):
        a = get_atom('a')
        b = get_atom('b')
        x = axiom1(a, b)
        self.assertEqual(str(x), 'Axiom1[a, b]')
        self.assertEqual(str(x.getAtom()), 'h_imply(a, h_imply(b, a))')

        y = axiom1(a, x)
        self.assertEqual(str(y), 'Axiom1[a, h_imply(a, h_imply(b, a))]')
        self.assertEqual(str(y.getAtom()), 'h_imply(a, h_imply(h_imply(a, h_imply(b, a)), a))')
    
    def test_axiom2(self):
        a = get_atom('a')
        b = get_atom('b')
        c = get_atom('c')
        x = axiom2(a, b, c)
        self.assertEqual(str(x), 'Axiom2[a, b, c]')
        self.assertEqual(str(x.getAtom()), 'h_imply(h_imply(a, h_imply(b, c)), h_imply(h_imply(a, b), h_imply(a, c)))')

    def test_axiom3(self):
        a = get_atom('a')
        b = get_atom('b')
        x = axiom3(a, b)
        self.assertEqual(str(x), 'Axiom3[a, b]')
        self.assertEqual(str(x.getAtom()), 'h_imply(h_imply(h_not(a), h_not(b)), h_imply(h_imply(h_not(a), b), a))')
    
    def test_assume(self):
        a = get_atom('a')
        x = assume(a)
        self.assertEqual(str(x), 'Assume[a]')
        self.assertEqual(str(x.getAtom()), 'a')

    
    def test_modus_ponens(self):
        a = get_atom('a')
        b = get_atom('b')
        x = mp(assume(a), assume(h_imply(a, b)))
        self.assertEqual(str(x), 'ModusPonens[Assume[a], Assume[h_imply(a, b)]]')
        self.assertEqual(str(x.getAtom()), 'b')
    
if __name__ == '__main__':
    unittest.main()