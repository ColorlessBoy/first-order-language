from __future__ import annotations
from util import type_check
from typing import Union
from atom import Atom, h_imply, h_not
from folatom import *

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
def reflexive(a: Atom) -> FolLemma:
    """ |=> a -> a. """
    b = h_imply(a, a)

    s1 = axiom1(a, a)
    s2 = axiom1(a, b)
    s3 = axiom2(a, b, a)
    s4 = modus_ponens(s1, modus_ponens(s2, s3))

    result = FolLemma('Reflexive')
    result.add(a)
    result.folatom = s4.getFolAtom()
    return result

@type_check(FolAtom)
def transitive(x: FolAtom, y: FolAtom) -> FolLemma:
    """ {x = (a -> b), y = (b -> c)} |=> (a -> c). """
    if x.getAtom().name != 'h_imply':
        raise ValueError("Require: x.getAtom().name == 'h_imply'.")
    if y.getAtom().name != 'h_imply':
        raise ValueError("Require: y.getAtom().name == 'h_imply'.")
    if x.getAtom().next[1] != y.getAtom().next[0]:
        raise ValueError("Require: x.getAtom().next[1] == y.getAtom().next[0].")
    
    a = x.getAtom().next[0]
    b = x.getAtom().next[1]
    c = y.getAtom().next[1]
    
    s1 = modus_ponens(y, axiom1(y, a))
    s2 = axiom2(a, b, c)
    s3 = modus_ponens(x, modus_ponens(s1, s2))

    result = FolLemma('Transitive')
    result.add(x)
    result.add(y)
    result.folatom = s3.getFolAtom()
    return result

@type_check(FolAtom)
def exchange(x: FolAtom) -> FolLemma:
    """ {x = a -> (b -> c)} |=> b -> (a -> c). """
    if x.getAtom().name != 'h_imply':
        raise ValueError("Require: x.getAtom().name == 'h_imply'.")
    if x.getAtom().next[1].name != 'h_imply':
        raise ValueError("Require: x.getAtom().next[1].name == 'h_imply'.")
    
    a = x.getAtom().next[0]
    b = x.getAtom().next[1].next[0]
    c = x.getAtom().next[1].next[1]

    s1 = axiom1(b, a)
    s2 = modus_ponens(x, axiom2(a, b, c))
    s3 = transitive(s1, s2)

    result = FolLemma('Exchange')
    result.add(x)
    result.folatom = s3.getFolAtom()
    return result

@type_check(FolAtom)
def deduction(assumption: FolAtom, y: FolAtom) -> FolLemma:
    """ Deduction Theorem: Assume[a] |=> b ===> |=> h_imply(a, b). """
    if assumption.name != 'Assume':
        """ x needs to be Assume(z). """
        raise ValueError('Required: x.name == "Assume"')
    
    if assumption == y:
        s = reflexive(assumption)
    elif y.name in ['Axiom1', 'Axiom2', 'Axiom3', 'Assume']:
        """ y is not based on assumption x. """
        s = modus_ponens(y, axiom1(y, assumption))
    else:
        """ y = modus_ponens(a, b). """
        s0 = deduction(assumption, y.next[0]) # h_imply(x, y.next[0]) without assumption x.
        s1 = deduction(assumption, y.next[1]) # h_imply(x, h_imply(y.next[0], y)) without assumption x.
        s2 = axiom2(assumption, y.next[0], y)
        s = modus_ponens(s0, modus_ponens(s1, s2))

    result = FolLemma('Deduction')
    result.add(assumption)
    result.add(y)
    result.folatom = s.getFolAtom()
    return result

@type_check(FolAtom)
def reduction(x: FolAtom, y: FolAtom) -> FolLemma:
    """ {h_imply(a, h_imply(b, c)), b} |=> h_imply(a, c). """
    """ {h_imply(a, h_imply(b, c)), b, Assume[a]} |=> c. """

    if x.getAtom().name != 'h_imply':
        raise ValueError("Require: x.getAtom().name == 'h_imply'.")
    if x.getAtom().next[1].name != 'h_imply':
        raise ValueError("Require: x.getAtom().next[1].name == 'h_imply'.")
    if x.getAtom().next[1].next[0] != y.getAtom():
        raise ValueError("Require: x.getAtom().next[1].next[0] == y")
    
    z = assume(x.getAtom().next[0])
    w = modus_ponens(y, modus_ponens(z, x))
    s = deduction(z, w)

    result = FolLemma('Reduction')
    result.add(x)
    result.add(y)
    result.folatom = s.getFolAtom()
    return result

@type_check(Atom)
def fromdoublenot(a: Atom) -> FolLemma:
    """ ~~a -> a. """
    x1 = axiom3(a, h_not(a))
    x2 = reflexive(h_not(a))
    x3 = reduction(x1, x2)
    x4 = axiom1(h_not(h_not(a)), h_not(a))
    s = transitive(x4, x3)
    
    result = FolLemma('DoubleNot1')
    result.add(a)
    result.folatom = s.getFolAtom()
    return result
    
@type_check(Atom)
def todoublenot(a: Atom) -> FolLemma:
    """ a -> ~~a. """
    x1 = axiom3(h_not(h_not(a)), a)
    x2 = fromdoublenot(h_not(a))
    x3 = modus_ponens(x2, x1)
    x4 = axiom1(a, h_not(h_not(h_not(a))))
    s = transitive(x4, x3)

    result = FolLemma('DoubleNot2')
    result.add(a)
    result.folatom = s.getFolAtom()
    return result

@type_check(Atom)
def contraposition1(a: Atom, b: Atom) -> FolLemma:
    """ |=> (~a -> ~b) -> (b -> a). """
    s1 = axiom1(b, h_not(a))
    s2 = exchange(axiom3(a, b))
    s3 = exchange(transitive(s1, s2))

    result = FolLemma('Contraposition1')
    result.add(a)
    result.add(b)
    result.folatom = s3.getFolAtom()
    return result
    
@type_check(Atom)
def contraposition2(a: Atom, b: Atom) -> FolLemma:
    """ (a -> b) -> (~b -> ~a). """
    c = assume(h_imply(a, b))
    x1 = transitive(fromdoublenot(a), c) # h_imply(h_not(h_not(a)), b)
    x2 = transitive(x1, todoublenot(b)) # h_imply(h_not(h_not(a)), h_not(h_not(b)))
    x3 = contraposition1(h_not(a), h_not(b))
    x4 = modus_ponens(x2, x3) # h_imply(h_not(b), h_not(a))
    s = deduction(c, x4) # remove assume

    result = FolLemma('Contraposition2')
    result.add(a)
    result.add(b)
    result.folatom = s.getFolAtom()
    return result

@type_check(FolAtom)
def contradiction(x: FolAtom, y: FolAtom) -> FolLemma:
    """ {a -> b,  h_not(a) -> b} |=> b. """
    if x.getAtom().name != 'h_imply' or y.getAtom().name != 'h_imply':
        raise ValueError("Require: x.name == 'h_imply' and y.name == 'h_imply'")
    if y.getAtom().next[0].name != 'h_not':
        raise ValueError("Require: y.next[0].name != 'h_not'")
    if x.getAtom().next[0] != y.getAtom().next[0].next[0] or x.getAtom().next[1] != y.getAtom().next[1]:
        raise ValueError("Require: x.next[0] != y.next[0].next[0] or x.next[1] != y.next[1]")
    
    a, b = x.getAtom().next
    x1 = contraposition2(a, b) # (a -> b) -> (~b -> ~a)
    x2 = modus_ponens(x, x1) # (~b -> ~ a)
    x3 = contraposition2(h_not(a), b)
    x4 = modus_ponens(y, x3) # (~b -> ~~a)
    x5 = axiom3(b, h_not(a))
    x6 = modus_ponens(x4, x5)
    s = modus_ponens(x2, x6)

    result = FolLemma('Contradiction')
    result.add(x)
    result.add(y)
    result.folatom = s.getFolAtom()
    return result

@type_check(Atom)
def negativeimply(a: Atom, b: Atom) -> FolLemma:
    """ |=> a -> (~a -> b) """
    x1 = modus_ponens(assume(a), axiom1(a, h_not(b)))
    x2 = modus_ponens(assume(h_not(a)), axiom1(h_not(a), h_not(b)))
    x3 = axiom3(b, a)
    x4 = modus_ponens(x1, modus_ponens(x2, x3))
    x5 = deduction(assume(a), x4)
    s  = deduction(assume(h_not(a)), x5)

    result = FolLemma('NegativeImply')
    result.add(a)
    result.add(b)
    result.folatom = s.getFolAtom()
    return result


@type_check(Atom)
def orinductionleft(a: Atom, b: Atom) -> FolLemma:
    """|=> a -> (a | b) """
    x1 = negativeimply(h_not(a), b)
    x2 = todoublenot(a)
    s = transitive(x2, x1)

    result = FolLemma('OrInductionLeft')
    result.add(a)
    result.add(b)
    result.folatom = s.getFolAtom()
    return result

@type_check(Atom)
def orinductionright(a: Atom, b: Atom) -> FolLemma:
    """|=> a -> (b | a) """
    s = axiom1(a, h_not(b))
    result = FolLemma('OrInductionRight')
    result.add(a)
    result.add(b)
    result.folatom = s.getFolAtom()
    return result

@type_check(Atom)
def orcommutative(a: Atom, b: Atom) -> FolLemma:
    """|=> (a | b) -> (b | a). """
    x1 = assume(h_imply(h_not(a), b))
    x2 = modus_ponens(x1, contraposition2(h_not(a), b)) # h_imply(h_not(b), h_not(h_not(a)))
    x3 = transitive(x2, fromdoublenot(a)) # h_imply(h_not(b), a)
    s = deduction(x1, x3) # h_imply(h_imply(h_not(a), b), h_imply(h_not(b), a))

    result = FolLemma('OrCommutative')
    result.add(a)
    result.add(b)
    result.folatom = s.getFolAtom()
    return result

@type_check(Atom)
def andreductionleft(a: Atom, b: Atom) -> FolLemma:
    """ |=> (a & b) -> a. """
    x1 = negativeimply(a, h_not(b))
    x2 = contraposition2(h_not(a), h_imply(a, h_not(b)))
    x3 = modus_ponens(x1, x2) # h_imply(h_not(h_imply(a, h_not(b))), h_not(h_not(a)))
    x4 = fromdoublenot(a) # h_imply(h_not(h_not(a)), a)
    s = transitive(x3, x4)

    result = FolLemma('AndReductionLeft')
    result.add(a)
    result.add(b)
    result.folatom = s.getFolAtom()
    return result

@type_check(Atom)
def andreductionright(a: Atom, b: Atom) -> FolLemma:
    """ |=> (a & b) -> b. """
    x1 = axiom1(h_not(b), a)
    x2 = contraposition2(h_not(b), h_imply(a, h_not(b)))
    x3 = modus_ponens(x1, x2) # h_imply(h_not(h_imply(a, h_not(b))), h_not(h_not(b)))
    x4 = fromdoublenot(b) 
    s = transitive(x3, x4)

    result = FolLemma('AndReductionRight')
    result.add(a)
    result.add(b)
    result.folatom = s.getFolAtom()
    return result

@type_check(FolAtom)
def andintroduction(x: FolAtom, y: FolAtom) -> FolLemma:
    """ {x, y} |=> x & y. """

    x1 = reflexive(h_imply(x, h_not(y)))
    x2 = exchange(x1)
    x3 = contraposition2(h_imply(x, h_not(y)), h_not(y))
    x4 = transitive(x2, x3) # x -> (~~y -> ~(x -> ~y))
    x5 = modus_ponens(x, x4) # ~~y -> ~(x -> ~y)
    x6 = modus_ponens(y, todoublenot(y)) # ~~y
    s  = modus_ponens(x6, x5) # ~(x -> ~y) = x /\ y

    result = FolLemma('AndIntroduction')
    result.add(x)
    result.add(y)
    result.folatom = s.getFolAtom()
    return result
    
@type_check(FolAtom)
def andpair(x: FolAtom, y: FolAtom) -> FolLemma:
    """ {a -> c, b -> c} |=> (a & b -> c) """
    if x.getAtom().name != 'h_imply' or y.getAtom().name != 'h_imply':
        raise ValueError("Require: x.getAtom().name != 'h_imply' or y.getAtom().name != 'h_imply'")
    if x.getAtom().next[1] != y.getAtom().next[1]:
        raise ValueError("Require: x.getAtom().next[1] != y.getAtom().next[1]")
    
    a = x.getAtom().next[0]
    b = y.getAtom().next[0]
    c = y.getAtom().next[1]

    x1 = assume(h_imply(h_not(a), b))
    x2 = transitive(x1, y) # ~a -> c
    x3 = contradiction(x, x2) # c
    s = deduction(x1, x3)

    result = FolLemma('AndPair')
    result.add(x)
    result.add(y)
    result.folatom = s.getFolAtom()
    return result

@type_check(FolAtom)
def getassume(x: FolAtom) -> list[Atom]:
    if x.name in ['Axiom1', 'Axiom2', 'Axiom3']:
        return []
    elif x.name == 'Assume':
        return [x.getAtom()]
    else:
        result = []
        a = getassume(x.next[0])
        b = getassume(x.next[1])
        if a:
            result.extend(a)
        if b: 
            result.extend(b)
        return result

def replaceatom(x: Atom, assumptions: list[Atom]):
    if x.name == 'h_imply':
        return h_imply(replaceatom(x.next[0], assumptions), replaceatom(x.next[1], assumptions))
    elif x.name == 'h_not':
        return h_not(replaceatom(x.next[0]))
    else:
        if x in assumptions:
            return h_not(x)
        else:
            return x

def replaceassume(x: FolAtom, assumptions: list[Atom]) -> FolAtom:
    if x.name == 'Axiom1':
        a = replaceatom(x.next[0], assumptions)
        b = replaceatom(x.next[1], assumptions)
        return axiom1(a, b)
    elif x.name == 'Axiom2':
        a = replaceatom(x.next[0], assumptions)
        b = replaceatom(x.next[1], assumptions)
        c = replaceatom(x.next[2], assumptions)
        return axiom2(a, b, c)
    elif x.name == 'Axiom3':
        a = replaceatom(x.next[0], assumptions)
        b = replaceatom(x.next[1], assumptions)
        return axiom3(a, b)
    elif x.name == 'ModusPonens':
        a = replaceassume(x.next[0], assumptions)
        b = replaceassume(x.next[1], assumptions)
        return modus_ponens(a, b)
    else:
        return assume(replaceatom(x.next[0], assumptions))
    

        