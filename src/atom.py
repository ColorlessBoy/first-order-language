from __future__ import annotations
from util import type_check
from typing import Any

class Atom:
    def __init__(self, term: Any) -> None:
        """ Base type in this project """
        if isinstance(term, str):
            self.name = term
            self.next = []
        else:
            getAtom = getattr(term, "getAtom", None)
            if callable(getAtom):
                atom = term.getAtom()
                self.name = atom.name
                self.next = atom.next
            else:
                raise ValueError(f"Atom() can not accept {type(term)}.")
    
    def add(self, other:Atom) -> Atom:
        self.next.append(other)
        return self
    
    def getAtom(self) -> Atom:
        return self
    
    def __eq__(self, other:Atom) -> bool:
        if not isinstance(other, Atom):
            return False
        if self.name != other.name:
            return False
        if len(self.next) != len(other.next):
            return False
        for atom1, atom2 in zip(self.next, other.next):
            if atom1 != atom2:
                return False
        return True

    def __str__(self) -> str:
        result = self.name
        if len(self.next) > 0:
            result += '('
            for i, atom in enumerate(self.next):
                if i > 0:
                    result += ', '
                result += str(atom)
            result += ')'
        return result

base_atoms = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z']

@type_check(str)
def get_atom(atom: str) -> Atom:
    """ base_atoms = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z'] """
    if atom not in base_atoms:
        raise ValueError(f"The form does not contain base atom '{atom}'.")
    return Atom(atom)

@type_check(Atom)
def h_not(a: Atom) -> Atom:
    """ ~a """
    atom = Atom('h_not')
    atom.add(a)
    return atom

@type_check(Atom)
def h_imply(a: Atom, b: Atom) -> Atom:
    """ a -> b """
    atom = Atom('h_imply')
    atom.add(a)
    atom.add(b)
    return atom
