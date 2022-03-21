import sys
sys.path.append('.')
sys.path.append('./src')

import unittest
from atom import get_atom, h_not, h_imply

class AtomTest(unittest.TestCase):

    def test_get_atom(self):
        a = get_atom('a')
        self.assertEqual(str(a), 'a')
    
    def test_h_not(self):
        a = get_atom('a')
        b = h_not(a)
        self.assertEqual(str(b), 'h_not(a)')

    def test_h_imply(self):
        a = get_atom('a')
        b = get_atom('b')
        c = h_imply(a, b)
        self.assertEqual(str(c), 'h_imply(a, b)')

if __name__ == '__main__':
    unittest.main()