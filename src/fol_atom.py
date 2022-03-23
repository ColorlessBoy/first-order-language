from __future__ import annotations
from util import type_check
from typing import Any, Union
from atom import Atom, h_imply, h_not

class FolAtom():
    def __init__(self, term: Any) -> None:
        """ Base type in First Order Language. """
        if isinstance(term, str):
            self.name = term
            self.next = []
            self.atom = None
        else:
            getFolAtom = getattr(term, "getFolAtom", None)
            if callable(getFolAtom):
                folatom = term.getFolAtom()
                self.name = folatom.name
                self.next = folatom.next
                self.atom = folatom.atom
            else:
                raise ValueError(f"FolAtom() can not accept {type(term)}.")
    
    def add(self, other:Union[Atom, FolAtom]) -> FolAtom:
        self.next.append(other)
        return self
    
    def getAtom(self) -> Atom:
        return self.atom
    
    def getFolAtom(self) -> FolAtom:
        return self

    def __eq__(self, other:Union[Atom, FolAtom]) -> bool:
        if not isinstance(other, Union[Atom, FolAtom]):
            return False
        return self.getAtom() == other.getAtom()

    def __str__(self) -> str:
        result = self.name
        if len(self.next) > 0:
            result += '['
            for i, atom in enumerate(self.next):
                if i > 0:
                    result += ', '
                result += str(atom)
            result += ']'
        return result
    
@type_check(Atom)
def axiom1(a: Atom, b: Atom) -> FolAtom:
    """ Axiom1: a -> (b -> a). """
    a1 = h_imply(a, h_imply(b, a))
    result = FolAtom('Axiom1')
    result.add(a)
    result.add(b)
    result.atom = a1
    return result

@type_check(Atom)
def axiom2(a: Atom, b: Atom, c: Atom) -> FolAtom:
    """ Axiom2: (a -> (b -> c)) -> ((a -> b) -> (a -> c)). """
    a1 = h_imply(a, h_imply(b, c))
    a2 = h_imply(h_imply(a, b), h_imply(a, c))
    a3 = h_imply(a1, a2)
    result = FolAtom('Axiom2')
    result.add(a)
    result.add(b)
    result.add(c)
    result.atom = a3
    return result

@type_check(Atom)
def axiom3(a: Atom, b: Atom) -> FolAtom:
    """ Axiom3: ((~a) -> (~b)) -> ((~a -> b) -> a). """
    x = h_imply(h_not(a), h_not(b))
    y = h_imply(h_imply(h_not(a), b), a)
    z = h_imply(x, y)
    result = FolAtom('Axiom3')
    result.add(a)
    result.add(b)
    result.atom = z
    return result

@type_check(FolAtom)
def modus_ponens(a: FolAtom, b: FolAtom) -> FolAtom:
    """ Inference (Modus Ponens): {a, (a -> b)} => b """
    result = FolAtom('ModusPonens')
    result.add(a)
    result.add(b)
    if b.getAtom().name != 'h_imply':
        raise ValueError("Require: b.getAtom().name == 'h_imply'.")
    if len(b.getAtom().next) != 2:
        raise ValueError("Require: len(b.getAtom().next) == 2.")
    if a.getAtom() != b.getAtom().next[0]:
        raise ValueError("Require: a.getAtom() == b.getAtom().next[0].")
    result.atom = b.getAtom().next[1]
    return result

@type_check(Atom)
def assume(a: Atom) -> FolAtom:
    """ Construct assumption. """
    result = FolAtom('Assume')
    result.add(a)
    result.atom = a
    return result