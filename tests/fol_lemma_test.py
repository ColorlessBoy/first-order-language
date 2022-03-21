#!/usr/bin/env python
import sys
sys.path.append('.')
sys.path.append('./src')
import unittest
from fol_atom import get_assume
from fol_lemma import *

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
        x = get_assume(h_imply(a, b))
        y = get_assume(h_imply(b, c))
        l = lemma3(x, y)
        self.assertEqual(str(l), 'Lemma3{Assume[h_imply(a, b)], Assume[h_imply(b, c)]}')
        self.assertEqual(str(l.getFolAtom()), 'ModusPonens[Assume[h_imply(a, b)], ModusPonens[ModusPonens[Assume[h_imply(b, c)], Axiom1[h_imply(b, c), a]], Axiom2[a, b, c]]]')
        self.assertEqual(str(l.getAtom()), 'h_imply(a, c)')
    
    def test_lemma4(self):
        a = get_atom('a')
        b = get_atom('b')
        c = get_atom('c')
        x = get_assume(h_imply(a, h_imply(b, c)))
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

if __name__ == '__main__':
    unittest.main()