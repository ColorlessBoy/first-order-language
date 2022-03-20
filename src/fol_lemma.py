from typing import Union
from atom import Atom, get_atom, h_imply, h_not
from fol_atom import type_check, FolAtom, axiom1, axiom2, axiom3, modus_ponens as mp

@type_check(Union[Atom, FolAtom])
def lemma1(a: Union[Atom, FolAtom]) -> FolAtom:
    """ Lemma: a -> a """
    if isinstance(a, FolAtom):
        a = a.atom
    b = h_imply(a, a)
    x1 = axiom1(a, a)
    x2 = axiom1(a, b)
    x3 = axiom2(a, b, a)
    return mp(x1, mp(x2, x3))

@type_check(Union[Atom, FolAtom])
def lemma2(a: Union[Atom, FolAtom]) -> FolAtom:
    """ Lemma: ((~a -> a) -> a)"""
    if isinstance(a, FolAtom):
        a = a.atom
    b = h_not(a)
    x1 = lemma1(b)
    x2 = axiom3(a, a)
    return mp(x1, x2)

@type_check()
def lemma3(x: FolAtom, y: FolAtom) -> FolAtom:
    """ Lemma: \{x = (a -> b), y = (b -> c)\} => (a -> c). """
    if x.atom.content != 'h_imply':
        raise ValueError("Require: x.content == 'h_imply'.")
    if len(x.atom.next) != 2:
        raise ValueError("Require: len(x.next) == 2.")
    if y.atom.content != 'h_imply':
        raise ValueError("Require: y.content == 'h_imply'.")
    if len(y.atom.next) != 2:
        raise ValueError("Require: len(y.next) == 2.")
    if x.atom.next[1] != y.atom.next[0]:
        raise ValueError("Require: x.next[1] = y.next[0].")
    
    a = x.atom.next[0]
    b = x.atom.next[1]
    c = y.atom.next[1]
    
    x1 = mp(y, axiom1(y, a))
    x2 = axiom2(a, b, c)
    return mp(x, mp(x1, x2))

@type_check()
def lemma4(x: FolAtom) -> FolAtom:
    """ Lemma: \{x = a -> (b -> c)\} => b -> (a -> c). """
    if x.atom.content != 'h_imply':
        raise ValueError("Require: x.content == 'h_imply'.")
    if len(x.atom.next) != 2:
        raise ValueError("Require: len(x.next) == 2.")
    if x.atom.next[1].content != 'h_imply':
        raise ValueError("Require: x.atom.next[1].content == 'h_imply'.")
    if len(x.atom.next[1].next) != 2:
        raise ValueError("Require: len(x.atom.next[1].next) == 2.")
    
    a = x.atom.next[0]
    b = x.atom.next[1].next[0]
    c = x.atom.next[1].next[1]

    x1 = axiom1(b, a)
    x2 = mp(x, axiom2(a, b, c))
    return lemma3(x1, x2)

@type_check(Union[Atom, FolAtom])
def lemma5(a: Union[Atom, FolAtom], b: Union[Atom, FolAtom]) -> FolAtom:
    """ Lemma: (~a -> ~b) -> (b -> a). """
    if isinstance(a, FolAtom):
        a = a.atom
    if isinstance(b, FolAtom):
        b = b.atom
    x1 = axiom1(b, h_not(a))
    x2 = lemma4(axiom3(a, b))
    return lemma4(lemma3(x1, x2))


if __name__ == '__main__':
    a = get_atom('a')
    b = lemma1(a)
    print(b)

    a = get_atom('a')
    b = get_atom('b')
    c = get_atom('c')
    x = FolAtom(h_imply(a, b))
    y = FolAtom(h_imply(b, c))
    z = lemma3(x, y)
    print(z)

    a = get_atom('a')
    b = get_atom('b')
    c = get_atom('c')
    x = FolAtom(h_imply(a, h_imply(b, c)))
    print(lemma4(x))