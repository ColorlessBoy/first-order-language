#!/usr/bin/env python
import sys
sys.path.append('.')
sys.path.append('./src')
import unittest
from atom import get_atom
from folatom import *
from follemma import *

class FolLemmaTests(unittest.TestCase):

    def test_lemma1(self):
        a = get_atom('a')
        l = lemma1(a)
        self.assertEqual(str(l), 'Lemma1{a}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[Axiom1[a, a], ModusPonens[Axiom1[a, h_imply(a, a)], Axiom2[a, h_imply(a, a), a]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(a, a)')
    
    def test_lemma2(self):
        a = get_atom('a')
        l = lemma2(a)
        self.assertEqual(str(l), 'Lemma2{a}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[ModusPonens[Axiom1[h_not(a), h_not(a)], ModusPonens[Axiom1[h_not(a), h_imply(h_not(a), h_not(a))], Axiom2[h_not(a), h_imply(h_not(a), h_not(a)), h_not(a)]]], Axiom3[a, a]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(h_imply(h_not(a), a), a)')

    
    def test_lemma3(self):
        a = get_atom('a')
        b = get_atom('b')
        c = get_atom('c')
        x = assume(h_imply(a, b))
        y = assume(h_imply(b, c))
        l = lemma3(x, y)
        self.assertEqual(str(l), 'Lemma3{Assume[h_imply(a, b)], Assume[h_imply(b, c)]}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[Assume[h_imply(a, b)], ModusPonens[ModusPonens[Assume[h_imply(b, c)], Axiom1[h_imply(b, c), a]], Axiom2[a, b, c]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(a, c)')
    
    def test_lemma4(self):
        a = get_atom('a')
        b = get_atom('b')
        c = get_atom('c')
        x = assume(h_imply(a, h_imply(b, c)))
        l = lemma4(x)
        self.assertEqual(str(l), 'Lemma4{Assume[h_imply(a, h_imply(b, c))]}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[Axiom1[b, a], ModusPonens[ModusPonens[ModusPonens[Assume[h_imply(a, h_imply(b, c))], Axiom2[a, b, c]], Axiom1[h_imply(h_imply(a, b), h_imply(a, c)), b]], Axiom2[b, h_imply(a, b), h_imply(a, c)]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(b, h_imply(a, c))')

    def test_lemma5(self):
        a = get_atom('a')
        b = get_atom('b')
        l = lemma5(a, b)
        self.assertEqual(str(l), 'Lemma5{a, b}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[Axiom1[h_imply(h_not(a), h_not(b)), b], ModusPonens[ModusPonens[ModusPonens[ModusPonens[Axiom1[b, h_not(a)], ModusPonens[ModusPonens[ModusPonens[Axiom1[h_imply(h_not(a), b), h_imply(h_not(a), h_not(b))], ModusPonens[ModusPonens[ModusPonens[Axiom3[a, b], Axiom2[h_imply(h_not(a), h_not(b)), h_imply(h_not(a), b), a]], Axiom1[h_imply(h_imply(h_imply(h_not(a), h_not(b)), h_imply(h_not(a), b)), h_imply(h_imply(h_not(a), h_not(b)), a)), h_imply(h_not(a), b)]], Axiom2[h_imply(h_not(a), b), h_imply(h_imply(h_not(a), h_not(b)), h_imply(h_not(a), b)), h_imply(h_imply(h_not(a), h_not(b)), a)]]], Axiom1[h_imply(h_imply(h_not(a), b), h_imply(h_imply(h_not(a), h_not(b)), a)), b]], Axiom2[b, h_imply(h_not(a), b), h_imply(h_imply(h_not(a), h_not(b)), a)]]], Axiom2[b, h_imply(h_not(a), h_not(b)), a]], Axiom1[h_imply(h_imply(b, h_imply(h_not(a), h_not(b))), h_imply(b, a)), h_imply(h_not(a), h_not(b))]], Axiom2[h_imply(h_not(a), h_not(b)), h_imply(b, h_imply(h_not(a), h_not(b))), h_imply(b, a)]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(h_imply(h_not(a), h_not(b)), h_imply(b, a))')
    
    def test_lemma6(self):
        a = get_atom('a')
        b = get_atom('b')
        B = assume(h_imply(a, b))
        C = assume(h_imply(h_imply(a, b), a))
        D = mp(mp(B, C), B)
        l = lemma6(B, D)
        self.assertEqual(str(l), 'Lemma6{Assume[h_imply(a, b)], ModusPonens[ModusPonens[Assume[h_imply(a, b)], Assume[h_imply(h_imply(a, b), a)]], Assume[h_imply(a, b)]]}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[ModusPonens[ModusPonens[Axiom1[h_imply(a, b), h_imply(a, b)], ModusPonens[Axiom1[h_imply(a, b), h_imply(h_imply(a, b), h_imply(a, b))], Axiom2[h_imply(a, b), h_imply(h_imply(a, b), h_imply(a, b)), h_imply(a, b)]]], ModusPonens[ModusPonens[Assume[h_imply(h_imply(a, b), a)], Axiom1[h_imply(h_imply(a, b), a), h_imply(a, b)]], Axiom2[h_imply(a, b), h_imply(a, b), a]]], ModusPonens[ModusPonens[Axiom1[h_imply(a, b), h_imply(a, b)], ModusPonens[Axiom1[h_imply(a, b), h_imply(h_imply(a, b), h_imply(a, b))], Axiom2[h_imply(a, b), h_imply(h_imply(a, b), h_imply(a, b)), h_imply(a, b)]]], Axiom2[h_imply(a, b), a, b]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(h_imply(a, b), b)')
    
    def test_lemma7(self):
        a = get_atom('a')
        b = get_atom('b')
        c = get_atom('c')

        x = assume(h_imply(a, h_imply(b, c)))
        y = assume(b)

        l = lemma7(x, y)
        self.assertEqual(str(l), 'Lemma7{Assume[h_imply(a, h_imply(b, c))], Assume[b]}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[ModusPonens[Assume[b], Axiom1[b, a]], ModusPonens[ModusPonens[ModusPonens[Axiom1[a, a], ModusPonens[Axiom1[a, h_imply(a, a)], Axiom2[a, h_imply(a, a), a]]], ModusPonens[ModusPonens[Assume[h_imply(a, h_imply(b, c))], Axiom1[h_imply(a, h_imply(b, c)), a]], Axiom2[a, a, h_imply(b, c)]]], Axiom2[a, b, c]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(a, c)')

    def test_lemma8(self):
        a = get_atom('a')
        l = lemma8(a)
        self.assertEqual(str(l), 'Lemma8{a}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[Axiom1[h_not(h_not(a)), h_not(a)], ModusPonens[ModusPonens[ModusPonens[ModusPonens[ModusPonens[Axiom1[h_not(a), h_not(a)], Axiom1[h_imply(h_not(a), h_imply(h_not(a), h_not(a))), h_imply(h_not(a), h_not(h_not(a)))]], ModusPonens[ModusPonens[ModusPonens[Axiom1[h_not(a), h_imply(h_not(a), h_not(a))], Axiom1[h_imply(h_not(a), h_imply(h_imply(h_not(a), h_not(a)), h_not(a))), h_imply(h_not(a), h_not(h_not(a)))]], ModusPonens[ModusPonens[Axiom2[h_not(a), h_imply(h_not(a), h_not(a)), h_not(a)], Axiom1[h_imply(h_imply(h_not(a), h_imply(h_imply(h_not(a), h_not(a)), h_not(a))), h_imply(h_imply(h_not(a), h_imply(h_not(a), h_not(a))), h_imply(h_not(a), h_not(a)))), h_imply(h_not(a), h_not(h_not(a)))]], Axiom2[h_imply(h_not(a), h_not(h_not(a))), h_imply(h_not(a), h_imply(h_imply(h_not(a), h_not(a)), h_not(a))), h_imply(h_imply(h_not(a), h_imply(h_not(a), h_not(a))), h_imply(h_not(a), h_not(a)))]]], Axiom2[h_imply(h_not(a), h_not(h_not(a))), h_imply(h_not(a), h_imply(h_not(a), h_not(a))), h_imply(h_not(a), h_not(a))]]], ModusPonens[ModusPonens[ModusPonens[Axiom1[h_imply(h_not(a), h_not(h_not(a))), h_imply(h_not(a), h_not(h_not(a)))], ModusPonens[Axiom1[h_imply(h_not(a), h_not(h_not(a))), h_imply(h_imply(h_not(a), h_not(h_not(a))), h_imply(h_not(a), h_not(h_not(a))))], Axiom2[h_imply(h_not(a), h_not(h_not(a))), h_imply(h_imply(h_not(a), h_not(h_not(a))), h_imply(h_not(a), h_not(h_not(a)))), h_imply(h_not(a), h_not(h_not(a)))]]], ModusPonens[ModusPonens[Axiom3[a, h_not(a)], Axiom1[h_imply(h_imply(h_not(a), h_not(h_not(a))), h_imply(h_imply(h_not(a), h_not(a)), a)), h_imply(h_not(a), h_not(h_not(a)))]], Axiom2[h_imply(h_not(a), h_not(h_not(a))), h_imply(h_not(a), h_not(h_not(a))), h_imply(h_imply(h_not(a), h_not(a)), a)]]], Axiom2[h_imply(h_not(a), h_not(h_not(a))), h_imply(h_not(a), h_not(a)), a]]], Axiom1[h_imply(h_imply(h_not(a), h_not(h_not(a))), a), h_not(h_not(a))]], Axiom2[h_not(h_not(a)), h_imply(h_not(a), h_not(h_not(a))), a]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(h_not(h_not(a)), a)')

    def test_lemma9(self):
        a = get_atom('a')
        l = lemma9(a)
        self.assertEqual(str(l), 'Lemma9{a}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[Axiom1[a, h_not(h_not(h_not(a)))], ModusPonens[ModusPonens[ModusPonens[ModusPonens[Axiom1[h_not(h_not(h_not(a))), h_not(h_not(a))], ModusPonens[ModusPonens[ModusPonens[ModusPonens[ModusPonens[Axiom1[h_not(h_not(a)), h_not(h_not(a))], Axiom1[h_imply(h_not(h_not(a)), h_imply(h_not(h_not(a)), h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a))))]], ModusPonens[ModusPonens[ModusPonens[Axiom1[h_not(h_not(a)), h_imply(h_not(h_not(a)), h_not(h_not(a)))], Axiom1[h_imply(h_not(h_not(a)), h_imply(h_imply(h_not(h_not(a)), h_not(h_not(a))), h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a))))]], ModusPonens[ModusPonens[Axiom2[h_not(h_not(a)), h_imply(h_not(h_not(a)), h_not(h_not(a))), h_not(h_not(a))], Axiom1[h_imply(h_imply(h_not(h_not(a)), h_imply(h_imply(h_not(h_not(a)), h_not(h_not(a))), h_not(h_not(a)))), h_imply(h_imply(h_not(h_not(a)), h_imply(h_not(h_not(a)), h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(a))))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a))))]], Axiom2[h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_imply(h_imply(h_not(h_not(a)), h_not(h_not(a))), h_not(h_not(a)))), h_imply(h_imply(h_not(h_not(a)), h_imply(h_not(h_not(a)), h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(a))))]]], Axiom2[h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_imply(h_not(h_not(a)), h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(a)))]]], ModusPonens[ModusPonens[ModusPonens[Axiom1[h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a))))], ModusPonens[Axiom1[h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))))], Axiom2[h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a))))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a))))]]], ModusPonens[ModusPonens[Axiom3[h_not(a), h_not(h_not(a))], Axiom1[h_imply(h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_imply(h_not(h_not(a)), h_not(h_not(a))), h_not(a))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a))))]], Axiom2[h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_imply(h_not(h_not(a)), h_not(h_not(a))), h_not(a))]]], Axiom2[h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_imply(h_not(h_not(a)), h_not(h_not(a))), h_not(a)]]], Axiom1[h_imply(h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_not(a)), h_not(h_not(h_not(a)))]], Axiom2[h_not(h_not(h_not(a))), h_imply(h_not(h_not(a)), h_not(h_not(h_not(a)))), h_not(a)]]], Axiom3[h_not(h_not(a)), a]], Axiom1[h_imply(h_imply(h_not(h_not(h_not(a))), a), h_not(h_not(a))), a]], Axiom2[a, h_imply(h_not(h_not(h_not(a))), a), h_not(h_not(a))]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(a, h_not(h_not(a)))')

    def test_lemma10(self):
        a = get_atom('a')
        b = get_atom('b')
        l = lemma10(a, b)
        self.assertEqual(str(l), 'Lemma10{a, b}')
        self.assertEqual(str(l.getAtom()), 'h_imply(h_not(a), h_imply(a, b))')

    def test_lemma11(self):
        a = get_atom('a')
        b = get_atom('b')
        l = lemma11(a, b)
        self.assertEqual(str(l), 'Lemma11{a, b}')
        self.assertEqual(str(l.getAtom()), 'h_imply(h_imply(a, b), h_imply(h_not(b), h_not(a)))')

    def test_lemma12(self):
        a = get_atom('a')
        b = get_atom('b')
        l = lemma12(a, b)
        self.assertEqual(str(l), 'Lemma12{a, b}')
        self.assertEqual(str(l.getAtom()), 'h_imply(a, h_imply(h_not(b), h_not(h_imply(a, b))))')
    
    def test_lemma13(self):
        a = get_atom('a')
        b = get_atom('b')
        x = assume(h_imply(a, b))
        y = assume(h_imply(h_not(a), b))
        l = lemma13(x, y)
        self.assertEqual(str(l), 'Lemma13{Assume[h_imply(a, b)], Assume[h_imply(h_not(a), b)]}')
        self.assertEqual(str(l.getAtom()), 'b')
    
    def test_lemma14(self):
        a = get_atom('a')
        b = get_atom('b')
        x = lor(a, b)
        l = lemma14(a, x)
        self.assertEqual(str(l), 'Lemma14{a, b}')
        self.assertEqual(str(l.getAtom()), 'h_imply(a, h_imply(h_not(a), b))')

if __name__ == '__main__':
    unittest.main()