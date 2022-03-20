#!/usr/bin/env python
from ctypes.wintypes import tagRECT
import sys
import tarfile
sys.path.append('.')
sys.path.append('./src')
import unittest
from fol_lemma import *
from atom import Atom, get_atom, h_imply, h_not
from fol_atom import FolAtom

class FolLemmaTests(unittest.TestCase):

    def test_lemma1(self):
        a = get_atom('a')
        target = FolAtom(h_imply(a, a))
        self.assertEqual(lemma1(a), target)
    
    def test_lemma2(self):
        a = get_atom('a')
        target = FolAtom(h_imply(h_imply(h_not(a), a), a))
        self.assertEqual(lemma2(a), target)
    
    def test_lemma3(self):
        a = get_atom('a')
        b = get_atom('b')
        c = get_atom('c')
        x = FolAtom(h_imply(a, b))
        y = FolAtom(h_imply(b, c))
        target = FolAtom(h_imply(a, c))
        self.assertEqual(lemma3(x, y), target)
    
    def test_lemma4(self):
        a = get_atom('a')
        b = get_atom('b')
        c = get_atom('c')
        x = FolAtom(h_imply(a, h_imply(b, c)))
        target = FolAtom(h_imply(b, h_imply(a, c)))
        self.assertEqual(lemma4(x), target)

    def test_lemma5(self):
        a = get_atom('a')
        b = get_atom('b')
        target = FolAtom(h_imply(h_imply(h_not(a), h_not(b)), h_imply(b, a)))
        self.assertEqual(lemma5(a, b), target)

        

if __name__ == '__main__':
    unittest.main()