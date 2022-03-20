from __future__ import annotations

class Atom:
    def __init__(self, content: str) -> None:
        """ Base type in this project """
        self.content = content
        self.next = []
    
    def __iadd__(self, other:Atom) -> Atom:
        self.next.append(other)
        return self
    
    def __add__(self, other:Atom) -> Atom:
        a = Atom(self.content)
        a += other
        return a
    
    def __eq__(self, other:Atom) -> Atom:
        if self.content != other.content:
            return False
        if len(self.next) != len(other.next):
            return False
        for atom1, atom2 in zip(self.next, other.next):
            if atom1 != atom2:
                return False
        return True

    def __str__(self) -> str:
        result = self.content
        if len(self.next) > 0:
            result += '('
            for i, atom in enumerate(self.next):
                if i > 0:
                    result += ','
                result += atom.__str__()
            result += ')'
        return result

base_atoms = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z']
    
def get_atom(atom: str) -> Atom:
    """ base_atoms = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z'] """
    if atom not in base_atoms:
        raise ValueError(f"The form does not contain {atom} atom.")
    return Atom(atom)

def h_not(a: Atom) -> Atom:
    """ ~a """
    if not isinstance(a, Atom):
        raise TypeError(f'Arguments must be <class: Atom>.')
    atom = Atom('h_not')
    atom += a
    return atom

def h_imply(a: Atom, b: Atom) -> Atom:
    """ a -> b """
    if not isinstance(a, Atom) or not isinstance(b, Atom):
        raise TypeError(f'Arguments must be <class: Atom>.')
    atom = Atom('h_imply')
    atom += a
    atom += b
    return atom