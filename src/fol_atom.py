from __future__ import annotations
from functools import wraps
from typing import Union
from atom import Atom, h_imply, h_not

class FolAtom():
    def __init__(self, a: Atom) -> None:
        self.atom = a

    def __str__(self) -> str:
        return f'FolAtom: {self.atom.__str__()}'
    
    def __eq__(self, other:Atom) -> Atom:
        return self.atom == other.atom
    
def type_check(validType=FolAtom):
    def inner_type_check(func):
        @wraps(func)
        def head_check(*args):
            if args is not None:
                for arg in args:
                    if not isinstance(arg, validType):
                        raise TypeError(f"Arguments are required to be {validType}.")
            return func(*args)
        return head_check
    return inner_type_check

@type_check(Union[Atom, FolAtom])
def axiom1(a: Union[Atom, FolAtom], b: Union[Atom, FolAtom]) -> FolAtom:
    """ Axiom1: a -> (b -> a). """
    if isinstance(a, FolAtom):
        a = a.atom
    if isinstance(b, FolAtom):
        b = b.atom
    return FolAtom(h_imply(a, h_imply(b, a)))

@type_check(Union[Atom, FolAtom])
def axiom2(a: Union[Atom, FolAtom], b: Union[Atom, FolAtom], c: Union[Atom, FolAtom]) -> FolAtom:
    """ Axiom2: (a -> (b -> c)) -> ((a -> b) -> (a -> c)). """
    if isinstance(a, FolAtom):
        a = a.atom
    if isinstance(b, FolAtom):
        b = b.atom
    if isinstance(c, FolAtom):
        c = c.atom
    x = h_imply(a, h_imply(b, c))
    y = h_imply(h_imply(a, b), h_imply(a, c))
    return FolAtom(h_imply(x, y))

@type_check(Union[Atom, FolAtom])
def axiom3(a: Union[Atom, FolAtom], b: Union[Atom, FolAtom]) -> FolAtom:
    """ Axiom3: ((~a) -> (~b)) -> ((~a -> b) -> a). """
    if isinstance(a, FolAtom):
        a = a.atom
    if isinstance(b, FolAtom):
        b = b.atom
    x = h_imply(h_not(a), h_not(b))
    y = h_imply(h_imply(h_not(a), b), a)
    return FolAtom(h_imply(x, y))

@type_check()
def modus_ponens(a: FolAtom, b: FolAtom) -> FolAtom:
    """ Inference (Modus Ponens): {a, (a -> b)} => b """
    a = a.atom
    b = b.atom
    if b.content != 'h_imply':
        raise ValueError("Require: b.content == 'h_imply'.")
    if len(b.next) != 2:
        raise ValueError("Require: len(b.next) == 2.")
    if a != b.next[0]:
        raise ValueError("Require: a == b.next[0].")
    return FolAtom(b.next[1])