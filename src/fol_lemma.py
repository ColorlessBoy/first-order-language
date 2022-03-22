from __future__ import annotations
from unittest import result
from util import type_check
from typing import Union
from atom import Atom, get_atom, h_imply, h_not
from fol_atom import FolAtom, axiom1, axiom2, axiom3, modus_ponens as mp

class FolLemma:
    def __init__(self, name: str) -> None:
        self.name = name
        self.next = []
        self.folatom = None
    
    def add(self, other:Union[Atom, FolAtom, FolLemma]) -> FolLemma:
        self.next.append(other)
        return self
    
    def getAtom(self) -> Atom:
        return self.folatom.getAtom()
    
    def getFolAtom(self) -> FolAtom:
        return self.folatom
    
    def __eq__(self, other:Union[Atom, FolAtom, FolLemma]) -> bool:
        if not isinstance(other, Union[Atom, FolAtom, FolLemma]):
            return False
        return self.getAtom() == other.getAtom()

    def __str__(self) -> str:
        result = self.name
        if len(self.next) > 0:
            result += '{'
            for i, atom in enumerate(self.next):
                if i > 0:
                    result += ', '
                result += atom.__str__()
            result += '}'
        return result

@type_check(Atom)
def lemma1(a: Atom) -> FolLemma:
    """ Lemma: |=> a -> a. """
    b = h_imply(a, a)

    s1 = axiom1(a, a)
    s2 = axiom1(a, b)
    s3 = axiom2(a, b, a)
    s4 = mp(s1, mp(s2, s3))

    result = FolLemma('Lemma1')
    result.add(a)
    result.folatom = s4.getFolAtom()
    return result

@type_check(Atom)
def lemma2(a: Atom) -> FolLemma:
    """ Lemma: |=> ((~a -> a) -> a). """
    b = h_not(a)

    s1 = lemma1(b)
    s2 = axiom3(a, a)
    s3 = mp(s1, s2)

    result = FolLemma('Lemma2')
    result.add(a)
    result.folatom = s3.getFolAtom()
    return result

@type_check(FolAtom)
def lemma3(x: FolAtom, y: FolAtom) -> FolLemma:
    """ Lemma: {x = (a -> b), y = (b -> c)} |=> (a -> c). """
    if x.getAtom().name != 'h_imply':
        raise ValueError("Require: x.getAtom().name == 'h_imply'.")
    if len(x.getAtom().next) != 2:
        raise ValueError("Require: len(x.getAtom().next) == 2.")
    if y.getAtom().name != 'h_imply':
        raise ValueError("Require: y.getAtom().name == 'h_imply'.")
    if len(y.getAtom().next) != 2:
        raise ValueError("Require: len(y.getAtom().next) == 2.")
    if x.getAtom().next[1] != y.getAtom().next[0]:
        raise ValueError("Require: x.getAtom().next[1] == y.getAtom().next[0].")
    
    a = x.getAtom().next[0]
    b = x.getAtom().next[1]
    c = y.getAtom().next[1]
    
    s1 = mp(y, axiom1(y, a))
    s2 = axiom2(a, b, c)
    s3 = mp(x, mp(s1, s2))

    result = FolLemma('Lemma3')
    result.add(x)
    result.add(y)
    result.folatom = s3.getFolAtom()
    return result

@type_check(FolAtom)
def lemma4(x: FolAtom) -> FolLemma:
    """ Lemma: {x = a -> (b -> c)} |=> b -> (a -> c). """
    if x.getAtom().name != 'h_imply':
        raise ValueError("Require: x.getAtom().name == 'h_imply'.")
    if len(x.getAtom().next) != 2:
        raise ValueError("Require: len(x.getAtom().next) == 2.")
    if x.getAtom().next[1].name != 'h_imply':
        raise ValueError("Require: x.getAtom().next[1].name == 'h_imply'.")
    if len(x.getAtom().next[1].next) != 2:
        raise ValueError("Require: len(x.getAtom().next[1].next) == 2.")
    
    a = x.getAtom().next[0]
    b = x.getAtom().next[1].next[0]
    c = x.getAtom().next[1].next[1]

    s1 = axiom1(b, a)
    s2 = mp(x, axiom2(a, b, c))
    s3 = lemma3(s1, s2)

    result = FolLemma('Lemma4')
    result.add(x)
    result.folatom = s3.getFolAtom()
    return result

@type_check(Atom)
def lemma5(a: Atom, b: Atom) -> FolLemma:
    """ Lemma: |=> (~a -> ~b) -> (b -> a). """
    s1 = axiom1(b, h_not(a))
    s2 = lemma4(axiom3(a, b))
    s3 = lemma4(lemma3(s1, s2))

    result = FolLemma('Lemma5')
    result.add(a)
    result.add(b)
    result.folatom = s3.getFolAtom()
    return result

@type_check(FolAtom)
def lemma6(x: FolAtom, y: FolAtom) -> FolLemma:
    """ Deduction Theorem: Assume(x) |=> y ===> |=> h_imply(x, y). """
    if x.name != 'Assume':
        """ x needs to be Assume(z). """
        raise ValueError('Required: x.name == "Assume"')
    
    if x == y:
        s = lemma1(x)
    elif y.name in ['Axiom1', 'Axiom2', 'Axiom3', 'Assume']:
        """ y is not based on assumption x. """
        s = mp(y, axiom1(y, x))
    else:
        s0 = lemma6(x, y.next[0])
        s1 = lemma6(x, y.next[1])
        s2 = axiom2(x, y.next[0], y)
        s = mp(s0, mp(s1, s2))

    result = FolLemma('Lemma6')
    result.add(x)
    result.add(y)
    result.folatom = s.getFolAtom()
    return result