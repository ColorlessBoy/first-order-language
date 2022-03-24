#!/usr/bin/env python
import sys
sys.path.append('.')
sys.path.append('./src')
import unittest
from atom import get_atom
from folatom import *
from follemma import *

class FolLemmaTests(unittest.TestCase):

    def test_reflexive(self):
        a = get_atom('a')
        l = reflexive(a)
        self.assertEqual(str(l), 'Reflexive{a}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[Axiom1[a, a], ModusPonens[Axiom1[a, h_imply(a, a)], Axiom2[a, h_imply(a, a), a]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(a, a)')
    
    def test_transitive(self):
        a = get_atom('a')
        b = get_atom('b')
        c = get_atom('c')
        x = assume(h_imply(a, b))
        y = assume(h_imply(b, c))
        l = transitive(x, y)
        self.assertEqual(str(l), 'Transitive{Assume[h_imply(a, b)], Assume[h_imply(b, c)]}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[Assume[h_imply(a, b)], ModusPonens[ModusPonens[Assume[h_imply(b, c)], Axiom1[h_imply(b, c), a]], Axiom2[a, b, c]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(a, c)')
    
    def test_exchange(self):
        a = get_atom('a')
        b = get_atom('b')
        c = get_atom('c')
        x = assume(h_imply(a, h_imply(b, c)))
        l = exchange(x)
        self.assertEqual(str(l), 'Exchange{Assume[h_imply(a, h_imply(b, c))]}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[Axiom1[b, a], ModusPonens[ModusPonens[ModusPonens[Assume[h_imply(a, h_imply(b, c))], Axiom2[a, b, c]], Axiom1[h_imply(h_imply(a, b), h_imply(a, c)), b]], Axiom2[b, h_imply(a, b), h_imply(a, c)]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(b, h_imply(a, c))')

    def test_deduction(self):
        a = get_atom('a')
        b = get_atom('b')
        B = assume(h_imply(a, b))
        C = assume(h_imply(h_imply(a, b), a))
        D = modus_ponens(modus_ponens(B, C), B)
        l = deduction(B, D)
        self.assertEqual(str(l), 'Deduction{Assume[h_imply(a, b)], ModusPonens[ModusPonens[Assume[h_imply(a, b)], Assume[h_imply(h_imply(a, b), a)]], Assume[h_imply(a, b)]]}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[ModusPonens[ModusPonens[Axiom1[h_imply(a, b), h_imply(a, b)], ModusPonens[Axiom1[h_imply(a, b), h_imply(h_imply(a, b), h_imply(a, b))], Axiom2[h_imply(a, b), h_imply(h_imply(a, b), h_imply(a, b)), h_imply(a, b)]]], ModusPonens[ModusPonens[Assume[h_imply(h_imply(a, b), a)], Axiom1[h_imply(h_imply(a, b), a), h_imply(a, b)]], Axiom2[h_imply(a, b), h_imply(a, b), a]]], ModusPonens[ModusPonens[Axiom1[h_imply(a, b), h_imply(a, b)], ModusPonens[Axiom1[h_imply(a, b), h_imply(h_imply(a, b), h_imply(a, b))], Axiom2[h_imply(a, b), h_imply(h_imply(a, b), h_imply(a, b)), h_imply(a, b)]]], Axiom2[h_imply(a, b), a, b]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(h_imply(a, b), b)')
    
    def test_reduction(self):
        a = get_atom('a')
        b = get_atom('b')
        c = get_atom('c')

        x = assume(h_imply(a, h_imply(b, c)))
        y = assume(b)

        l = reduction(x, y)
        self.assertEqual(str(l), 'Reduction{Assume[h_imply(a, h_imply(b, c))], Assume[b]}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[ModusPonens[Assume[b], Axiom1[b, a]], ModusPonens[ModusPonens[ModusPonens[Axiom1[a, a], ModusPonens[Axiom1[a, h_imply(a, a)], Axiom2[a, h_imply(a, a), a]]], ModusPonens[ModusPonens[Assume[h_imply(a, h_imply(b, c))], Axiom1[h_imply(a, h_imply(b, c)), a]], Axiom2[a, a, h_imply(b, c)]]], Axiom2[a, b, c]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(a, c)')

    def test_doublenot1(self):
        a = get_atom('a')
        l = doublenot1(a)
        self.assertEqual(str(l), 'DoubleNot1{a}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[Axiom1[h_not(h_not(a)), h_not(a)], ModusPonens[ModusPonens[ModusPonens[ModusPonens[ModusPonens[Axiom1[h_not(a), h_not(a)], Axiom1[h_imply(h_not(a), h_imply(h_not(a), h_not(a))), h_imply(h_not(a), h_not(h_not(a)))]], ModusPonens[ModusPonens[ModusPonens[Axiom1[h_not(a), h_imply(h_not(a), h_not(a))], Axiom1[h_imply(h_not(a), h_imply(h_imply(h_not(a), h_not(a)), h_not(a))), h_imply(h_not(a), h_not(h_not(a)))]], ModusPonens[ModusPonens[Axiom2[h_not(a), h_imply(h_not(a), h_not(a)), h_not(a)], Axiom1[h_imply(h_imply(h_not(a), h_imply(h_imply(h_not(a), h_not(a)), h_not(a))), h_imply(h_imply(h_not(a), h_imply(h_not(a), h_not(a))), h_imply(h_not(a), h_not(a)))), h_imply(h_not(a), h_not(h_not(a)))]], Axiom2[h_imply(h_not(a), h_not(h_not(a))), h_imply(h_not(a), h_imply(h_imply(h_not(a), h_not(a)), h_not(a))), h_imply(h_imply(h_not(a), h_imply(h_not(a), h_not(a))), h_imply(h_not(a), h_not(a)))]]], Axiom2[h_imply(h_not(a), h_not(h_not(a))), h_imply(h_not(a), h_imply(h_not(a), h_not(a))), h_imply(h_not(a), h_not(a))]]], ModusPonens[ModusPonens[ModusPonens[Axiom1[h_imply(h_not(a), h_not(h_not(a))), h_imply(h_not(a), h_not(h_not(a)))], ModusPonens[Axiom1[h_imply(h_not(a), h_not(h_not(a))), h_imply(h_imply(h_not(a), h_not(h_not(a))), h_imply(h_not(a), h_not(h_not(a))))], Axiom2[h_imply(h_not(a), h_not(h_not(a))), h_imply(h_imply(h_not(a), h_not(h_not(a))), h_imply(h_not(a), h_not(h_not(a)))), h_imply(h_not(a), h_not(h_not(a)))]]], ModusPonens[ModusPonens[Axiom3[a, h_not(a)], Axiom1[h_imply(h_imply(h_not(a), h_not(h_not(a))), h_imply(h_imply(h_not(a), h_not(a)), a)), h_imply(h_not(a), h_not(h_not(a)))]], Axiom2[h_imply(h_not(a), h_not(h_not(a))), h_imply(h_not(a), h_not(h_not(a))), h_imply(h_imply(h_not(a), h_not(a)), a)]]], Axiom2[h_imply(h_not(a), h_not(h_not(a))), h_imply(h_not(a), h_not(a)), a]]], Axiom1[h_imply(h_imply(h_not(a), h_not(h_not(a))), a), h_not(h_not(a))]], Axiom2[h_not(h_not(a)), h_imply(h_not(a), h_not(h_not(a))), a]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(h_not(h_not(a)), a)')

    def test_doublenot2(self):
        a = get_atom('a')
        l = doublenot2(a)
        self.assertEqual(str(l), 'DoubleNot2{a}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[Axiom1[a, h_not(h_not(h_not(a)))], ModusPonens[ModusPonens[ModusPonens[ModusPonens[Axiom1[h_not(h_not(h_not(a))), h_not(h_not(a))], ModusPonens[ModusPonens[ModusPonens[ModusPonens[ModusPonens[Axiom1[h_not(h_not(a)), h_not(h_not(a))], Axiom1[h_imply(h_not(h_not(a)), h_imply(h_not(h_not(a)), h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a))))]], ModusPonens[ModusPonens[ModusPonens[Axiom1[h_not(h_not(a)), h_imply(h_not(h_not(a)), h_not(h_not(a)))], Axiom1[h_imply(h_not(h_not(a)), h_imply(h_imply(h_not(h_not(a)), h_not(h_not(a))), h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a))))]], ModusPonens[ModusPonens[Axiom2[h_not(h_not(a)), h_imply(h_not(h_not(a)), h_not(h_not(a))), h_not(h_not(a))], Axiom1[h_imply(h_imply(h_not(h_not(a)), h_imply(h_imply(h_not(h_not(a)), h_not(h_not(a))), h_not(h_not(a)))), h_imply(h_imply(h_not(h_not(a)), h_imply(h_not(h_not(a)), h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(a))))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a))))]], Axiom2[h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_imply(h_imply(h_not(h_not(a)), h_not(h_not(a))), h_not(h_not(a)))), h_imply(h_imply(h_not(h_not(a)), h_imply(h_not(h_not(a)), h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(a))))]]], Axiom2[h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_imply(h_not(h_not(a)), h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(a)))]]], ModusPonens[ModusPonens[ModusPonens[Axiom1[h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a))))], ModusPonens[Axiom1[h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))))], Axiom2[h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a))))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a))))]]], ModusPonens[ModusPonens[Axiom3[h_not(a), h_not(h_not(a))], Axiom1[h_imply(h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_imply(h_not(h_not(a)), h_not(h_not(a))), h_not(a))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a))))]], Axiom2[h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_imply(h_not(h_not(a)), h_not(h_not(a))), h_not(a))]]], Axiom2[h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(a))), h_not(a)]]], Axiom1[h_imply(h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_not(a)), h_not(h_not(h_not(a)))]], Axiom2[h_not(h_not(h_not(a))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_not(a)]]], Axiom3[h_not(h_not(a)), a]], Axiom1[h_imply(h_imply(h_not(h_not(h_not(a))), a), h_not(h_not(a))), a]], Axiom2[a, h_imply(h_not(h_not(h_not(a))), a), h_not(h_not(a))]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(a, h_not(h_not(a)))')

    def test_contraposition1(self):
        a = get_atom('a')
        b = get_atom('b')
        l = contraposition1(a, b)
        self.assertEqual(str(l), 'Contraposition1{a, b}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[Axiom1[h_imply(h_not(a), h_not(b)), b], ModusPonens[ModusPonens[ModusPonens[ModusPonens[Axiom1[b, h_not(a)], ModusPonens[ModusPonens[ModusPonens[Axiom1[h_imply(h_not(a), b), h_imply(h_not(a), h_not(b))], ModusPonens[ModusPonens[ModusPonens[Axiom3[a, b], Axiom2[h_imply(h_not(a), h_not(b)), h_imply(h_not(a), b), a]], Axiom1[h_imply(h_imply(h_imply(h_not(a), h_not(b)), h_imply(h_not(a), b)), h_imply(h_imply(h_not(a), h_not(b)), a)), h_imply(h_not(a), b)]], Axiom2[h_imply(h_not(a), b), h_imply(h_imply(h_not(a), h_not(b)), h_imply(h_not(a), b)), h_imply(h_imply(h_not(a), h_not(b)), a)]]], Axiom1[h_imply(h_imply(h_not(a), b), h_imply(h_imply(h_not(a), h_not(b)), a)), b]], Axiom2[b, h_imply(h_not(a), b), h_imply(h_imply(h_not(a), h_not(b)), a)]]], Axiom2[b, h_imply(h_not(a), h_not(b)), a]], Axiom1[h_imply(h_imply(b, h_imply(h_not(a), h_not(b))), h_imply(b, a)), h_imply(h_not(a), h_not(b))]], Axiom2[h_imply(h_not(a), h_not(b)), h_imply(b, h_imply(h_not(a), h_not(b))), h_imply(b, a)]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(h_imply(h_not(a), h_not(b)), h_imply(b, a))')
    
    def test_contrapostion2(self):
        a = get_atom('a')
        b = get_atom('b')
        l = contraposition2(a, b)
        self.assertEqual(str(l), 'Contraposition2{a, b}')
        self.assertEqual(str(l.getAtom()), 'h_imply(h_imply(a, b), h_imply(h_not(b), h_not(a)))')
    
    def test_contradiction(self):
        a = get_atom('a')
        b = get_atom('b')
        x = assume(h_imply(a, b))
        y = assume(h_imply(h_not(a), b))
        l = contradiction(x, y)
        self.assertEqual(str(l), 'Contradiction{Assume[h_imply(a, b)], Assume[h_imply(h_not(a), b)]}')
        self.assertEqual(str(l.getAtom()), 'b')
    
    def test_orinductionleft(self):
        a = get_atom('a')
        b = get_atom('b')
        l = orinductionleft(a, b)
        self.assertEqual(str(l), 'OrInductionLeft{a, b}')
        self.assertEqual(str(l.getAtom()), 'h_imply(a, h_imply(h_not(a), b))')

    def test_orinductionright(self):
        a = get_atom('a')
        b = get_atom('b')
        l = orinductionright(a, b)
        self.assertEqual(str(l), 'OrInductionRight{a, b}')
        self.assertEqual(str(l.getAtom()), 'h_imply(a, h_imply(h_not(b), a))')
    
    def test_orcommutative(self):
        a = get_atom('a')
        b = get_atom('b')
        l = orcommutative(a, b)
        self.assertEqual(str(l), 'OrCommutative{a, b}')
        self.assertEqual(str(l.getAtom()), 'h_imply(h_imply(h_not(a), b), h_imply(h_not(b), a))')

    def test_andreductionleft(self):
        a = get_atom('a')
        b = get_atom('b')
        l = andreductionleft(a, b)
        self.assertEqual(str(l), 'AndReductionLeft{a, b}')
        self.assertEqual(str(l.getAtom()), 'h_imply(h_not(h_imply(a, h_not(b))), a)')

    def test_andreductionright(self):
        a = get_atom('a')
        b = get_atom('b')
        l = andreductionright(a, b)
        self.assertEqual(str(l), 'AndReductionRight{a, b}')
        self.assertEqual(str(l.getAtom()), 'h_imply(h_not(h_imply(a, h_not(b))), b)')
    
    def test_andintroduction(self):
        x = assume(get_atom('a'))
        y = assume(get_atom('b'))
        l = andintroduction(x, y)
        self.assertEqual(str(l), 'AndIntroduction{Assume[a], Assume[b]}')
        self.assertEqual(str(l.getAtom()), 'h_not(h_imply(a, h_not(b)))')

if __name__ == '__main__':
    unittest.main()