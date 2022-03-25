from unittest import result
from atom import *
from folatom import *
from follemma import *

@type_check(Atom)
def complete(a: Atom) -> FolLemma:
    folatom1 = atom2FolAtom(a)
    assumptions = getassume(folatom1)

    for assumption in assumptions:
        folatom2 = replaceassume(folatom1, assumption)
        x1 = deduction(assume(assumption), folatom1)
        x2 = deduction(assume(h_not(assumption)), folatom2)
        x3 = assume(h_imply(folatom2, folatom1)) # wrong, folatom1 remove assumption implicitly
        x4 = transitive(x2, x3)
        folatom1 = contradiction(x1, x4)
    
    result = FolLemma('Complete')
    result.add(a)
    result.folatom = folatom1.getFolAtom()
    return result

@type_check(Atom)
def atom2FolAtom(a: Atom) -> FolAtom:
    """ Return a or h_not(a), which is tautology. """
    s = None
    if a.name == 'h_not':
        x = atom2FolAtom(a.next[0])
        if x.getAtom() == a:
            s = x.getFolAtom() # return a
        else:
            s = todoublenot(x).getFolAtom() # return ~a
    elif a.name == 'h_imply':
        if a.next[0] == a.next[1]:
            s = reflexive(a.next[0], a.next[1]).getFolAtom() # return a
        else:
            x = atom2FolAtom(a.next[0])
            if x.getAtom() == a.next[0]:
                # x = a0
                y = atom2FolAtom(a.next[1]) # must be valid.
                if y.getAtom() == a.next[1]:
                    # y = a1
                    s = modus_ponens(y, axiom1(y, a.next[0])) # return a
                else:
                    # y = ~a1
                    # return {a0, ~a1} |=> ~(a0 -> a1)
                    x1 = exchange(reflexive(a)) # a0 -> ((a0 -> a1) -> a1)
                    x2 = contraposition2(a, a.next[1]) # ((a0 -> a1) -> a1) -> (~a1 -> ~(a0 -> a1))
                    x3 = transitive(x1, x2) # a0 -> (~a1 -> ~(a0 -> a1))
                    s  = modus_ponens(x, modus_ponens(y, x3)) # return ~a
            else:
                # x = ~a0
                x1 = modus_ponens(x, negativeimply(x, a.next[1])) # ~~a0 -> a1
                s = transitive(todoublenot(a.next[0]), x1).getFolAtom() # return a
    if s:
        result = FolLemma('atom2FolAtom')
        result.add(a)
        result.folatom = s.getFolAtom()
        return result

    return assume(a)

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

@type_check(Atom)
def replaceatom(x: Atom, assumption: Atom):
    if x.name == 'h_imply':
        return h_imply(replaceatom(x.next[0], assumption), replaceatom(x.next[1], assumption))
    elif x.name == 'h_not':
        return h_not(replaceatom(x.next[0]))
    elif x == assumption:
        return h_not(x)
    else:
        return x

@type_check([FolAtom, Atom])
def replaceassume(x: FolAtom, assumption: Atom) -> FolAtom:
    if x.name == 'Axiom1':
        a = replaceatom(x.next[0], assumption)
        b = replaceatom(x.next[1], assumption)
        return axiom1(a, b)
    elif x.name == 'Axiom2':
        a = replaceatom(x.next[0], assumption)
        b = replaceatom(x.next[1], assumption)
        c = replaceatom(x.next[2], assumption)
        return axiom2(a, b, c)
    elif x.name == 'Axiom3':
        a = replaceatom(x.next[0], assumption)
        b = replaceatom(x.next[1], assumption)
        return axiom3(a, b)
    elif x.name == 'ModusPonens':
        a = replaceassume(x.next[0], assumption)
        b = replaceassume(x.next[1], assumption)
        return modus_ponens(a, b)
    else:
        return assume(replaceatom(x.next[0], assumption))
    