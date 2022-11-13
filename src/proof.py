from __future__ import annotations

from prop import ForallProp, ImplyProp, NotProp, Prop, VarProp
from variable import Variable


class Proof:
    def __init__(self, p: Prop):
        self.prop = p

    def __eq__(self, proof: Proof) -> bool:
        return self.prop == proof.prop

    def __str__(self) -> str:
        return "Proof" + self.prop.__str__()


def axiom1(p1: Prop, p2: Prop) -> Proof:
    """axiom1

    Args:
        p1 (Prop): any prop
        p2 (Prop): any prop

    Returns:
        Proof: p1 => (p2 => p1)
    """
    p = ImplyProp(p1, ImplyProp(p2, p1))
    return Proof(p)


def axiom2(p1: Prop, p2: Prop, p3: Prop) -> Proof:
    """axiom2

    Args:
        p1 (Prop): any prop
        p2 (Prop): any prop
        p3 (Prop): any prop

    Returns:
        Proof: (p1 => (p2 => p3)) => ((p1 => p2) => (p1 => p3))
    """
    p4 = ImplyProp(p1, ImplyProp(p2, p3))
    p5 = ImplyProp(ImplyProp(p1, p2), ImplyProp(p1, p3))
    p6 = ImplyProp(p4, p5)
    return Proof(p6)


def axiom3(p1: Prop, p2: Prop) -> Proof:
    """axiom3

    Args:
        p1 (Prop): any prop
        p2 (Prop): any prop

    Returns:
        Proof: (!p1 => !p2) => ((!p1 => p2) => p1)
    """
    p3 = ImplyProp(NotProp(p1), NotProp(p2))
    p4 = ImplyProp(NotProp(p1), p2)
    p5 = ImplyProp(p3, ImplyProp(p4, p1))
    return Proof(p5)


def axiom4(p: Prop, x: Variable, y: Variable) -> Proof:
    """axiom4

    Args:
        p (Prop): any prop
        x (Variable): any variable
        y (Variable): y should not be bounded in p

    Raises:
        ValueError: axiom4(): y should not be bounded in p

    Returns:
        Proof: \forall x, p => p[x -> y]
    """
    if p.isbounded(y):
        raise ValueError("axiom4(): y should not be bounded in p")
    p1 = ForallProp(x, p)
    p2 = p.substitute(x, y)
    p3 = ImplyProp(p1, p2)
    return Proof(p3)


def axiom5(p1: Prop, p2: Prop, x: Variable) -> Proof:
    """axiom5

    Args:
        p1 (Prop): any prop
        p2 (Prop): any prop
        x (Variable): x should not be free in p1

    Raises:
        ValueError: axiom5(): x should not be free in p1

    Returns:
        Proof: (\forall x, p1 => p2) => (p1 => \forall p2)
    """
    if p1.isfree(x):
        raise ValueError("axiom5(): x should not be free in p1")
    p3 = ForallProp(x, ImplyProp(p1, p2))
    p4 = ImplyProp(p1, ForallProp(x, p2))
    p5 = ImplyProp(p3, p4)
    return Proof(p5)


def mp(proof1: Proof, proof2: Proof) -> Proof:
    """Modus ponens

    Args:
        proof1 (Proof): proof(a)
        proof2 (Proof): proof(a => b)

    Raises:
        ValueError: mp(): proof2.prop should be an ImplyProp
        ValueError: mp(): proof1 != proof2.prop.left_child

    Returns:
        Proof: proof(b)
    """
    if proof2.prop.name != "ImplyProp":
        raise ValueError("mp(): proof2.prop should be an ImplyProp")
    p: ImplyProp = proof2.prop  # type: ignore
    if proof1.prop != p.left_child:
        raise ValueError("mp(): proof1.prop != proof2.prop.left_child")
    return Proof(p.right_child)


def gen(proof: Proof, x: Variable) -> Proof:
    """Generalization

    Args:
        proof (Proof): proof(a)
        x (Variable): any variable

    Returns:
        Proof: \forall x a
    """
    return Proof(ForallProp(x, proof.prop))
