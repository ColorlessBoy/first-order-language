from __future__ import annotations
from unicodedata import name
from unittest import result
from util import type_check
from typing import Union
from atom import Atom, h_imply, h_not
from folatom import FolAtom, axiom1, axiom2, axiom3, assume, modus_ponens as mp

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
def lemma6(asm: FolAtom, y: FolAtom) -> FolLemma:
    """ Deduction Theorem: Assume[a] |=> b ===> |=> h_imply(a, b). """
    if asm.name != 'Assume':
        """ x needs to be Assume(z). """
        raise ValueError('Required: x.name == "Assume"')
    
    if asm == y:
        s = lemma1(asm)
    elif y.name in ['Axiom1', 'Axiom2', 'Axiom3', 'Assume']:
        """ y is not based on assumption x. """
        s = mp(y, axiom1(y, asm))
    else:
        s0 = lemma6(asm, y.next[0]) # h_imply(x, y.next[0]) without assumption x.
        s1 = lemma6(asm, y.next[1]) # h_imply(x, h_imply(y.next[0], y)) without assumption x.
        s2 = axiom2(asm, y.next[0], y)
        s = mp(s0, mp(s1, s2))

    result = FolLemma('Lemma6')
    result.add(asm)
    result.add(y)
    result.folatom = s.getFolAtom()
    return result

@type_check(FolAtom)
def lemma7(x: FolAtom, y: FolAtom) -> FolLemma:
    """ \{h_imply(a, h_imply(b, c)), b\} |=> h_imply(a, c). """
    """ \{h_imply(a, h_imply(b, c)), b, Assume[a]\} |=> c. """

    if x.getAtom().name != 'h_imply':
        raise ValueError("Require: x.getAtom().name == 'h_imply'.")
    if x.getAtom().next[1].name != 'h_imply':
        raise ValueError("Require: x.getAtom().next[1].name == 'h_imply'.")
    if x.getAtom().next[1].next[0] != y.getAtom():
        raise ValueError("Require: x.getAtom().next[1].next[0] == y")
    
    z = assume(x.getAtom().next[0])
    w = mp(y, mp(z, x))
    s = lemma6(z, w)

    result = FolLemma('Lemma7')
    result.add(x)
    result.add(y)
    result.folatom = s.getFolAtom()
    return result

@type_check(Atom)
def lemma8(a: Atom) -> FolAtom:
    """ h_imply(h_not(h_not(a)), a). """
    x1 = axiom3(a, h_not(a))
    x2 = lemma1(h_not(a))
    x3 = lemma7(x1, x2)
    x4 = axiom1(h_not(h_not(a)), h_not(a))
    s = lemma3(x4, x3)
    
    result = FolLemma('Lemma8')
    result.add(a)
    result.folatom = s.getFolAtom()
    return result
    
@type_check(Atom)
def lemma9(a: Atom) -> FolAtom:
    """ h_imply(a, h_not(h_not(a))). """
    x1 = axiom3(h_not(h_not(a)), a)
    x2 = lemma8(h_not(a))
    x3 = mp(x2, x1)
    x4 = axiom1(a, h_not(h_not(h_not(a))))
    s = lemma3(x4, x3)

    result = FolLemma('Lemma9')
    result.add(a)
    result.folatom = s.getFolAtom()
    return result

@type_check(Atom)
def lemma10(a: Atom, b: Atom) -> FolAtom:
    """ h_imply(h_not(a), h_imply(a, b)). """
    x1 = mp(assume(a), axiom1(a, h_not(b)))
    x2 = mp(assume(h_not(a)), axiom1(h_not(a), h_not(b)))
    x3 = axiom3(b, a)
    x4 = mp(x1, mp(x2, x3))
    x5 = lemma6(assume(a), x4)
    s  = lemma6(assume(h_not(a)), x5)

    result = FolLemma('Lemma10')
    result.add(a)
    result.add(b)
    result.folatom = s.getFolAtom()
    return result
    
@type_check(Atom)
def lemma11(a: Atom, b: Atom) -> FolAtom:
    """ h_imply(h_imply(a, b), h_imply(h_not(b), h_not(a))). """
    c = assume(h_imply(a, b))
    x1 = lemma3(lemma8(a), c) # h_imply(h_not(h_not(a)), b)
    x2 = lemma3(x1, lemma9(b)) # h_imply(h_not(h_not(a)), h_not(h_not(b)))
    x3 = lemma5(h_not(a), h_not(b))
    x4 = mp(x2, x3) # h_imply(h_not(b), h_not(a))
    s = lemma6(c, x4) # remove assume

    result = FolLemma('Lemma11')
    result.add(a)
    result.add(b)
    result.folatom = s.getFolAtom()
    return result

@type_check(Atom)
def lemma12(a: Atom, b: Atom) -> FolAtom:
    """ h_imply(a, h_imply(h_not(b), h_not(h_imply(a, b)))). """
    x1 = lemma1(h_imply(a, b))
    x2 = lemma4(x1)
    x3 = lemma11(h_imply(a, b), b)
    s = lemma3(x2, x3)

    result = FolLemma('Lemma12')
    result.add(a)
    result.add(b)
    result.folatom = s.getFolAtom()
    return result

@type_check(FolAtom)
def lemma13(x: FolAtom, y: FolAtom) -> FolAtom:
    """ \{x = h_imply(a, b), y = h_imply(h_not(a), b) \} |=> b. """
    if x.getAtom().name != 'h_imply' or y.getAtom().name != 'h_imply':
        raise ValueError("Require: x.name == 'h_imply' and y.name == 'h_imply'")
    if y.getAtom().next[0].name != 'h_not':
        raise ValueError("Require: y.next[0].name != 'h_not'")
    if x.getAtom().next[0] != y.getAtom().next[0].next[0] or x.getAtom().next[1] != y.getAtom().next[1]:
        raise ValueError("Require: x.next[0] != y.next[0].next[0] or x.next[1] != y.next[1]")
    
    a, b = x.getAtom().next
    x1 = lemma11(a, b) # (a -> b) -> (~b -> ~a)
    x2 = mp(x, x1) # (~b -> ~ a)
    x3 = lemma11(h_not(a), b)
    x4 = mp(y, x3) # (~b -> ~~a)
    x5 = axiom3(b, h_not(a))
    x6 = mp(x4, x5)
    s = mp(x2, x6)

    result = FolLemma('Lemma13')
    result.add(x)
    result.add(y)
    result.folatom = s.getFolAtom()
    return result

@type_check([Atom, FolAtom])
def lemma14(a: Atom, x: FolAtom) -> FolAtom:
    """|=> a -> (a \/ b) """
    if x.name != 'LogicOr':
        raise ValueError("Requrie: x.name == 'LogicOr'.")
    if a != x.next[0]:
        raise ValueError("Require: a == b.next[0].")
    
    b = x.next[1]
    x1 = lemma10(h_not(a), b)
    x2 = lemma9(a)
    s = lemma3(x2, x1)
    result = FolLemma('Lemma14')
    result.add(a)
    result.add(b)
    result.folatom = s.getFolAtom()
    return result