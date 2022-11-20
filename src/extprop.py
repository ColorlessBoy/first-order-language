from __future__ import annotations

from proof import Proof
from prop import ForallProp, ImplyProp, NotProp, Prop, Variable


class ExtProp(Prop):
    def __init__(self, p: Prop) -> None:
        super().__init__()
        self.prop = p

    def eval(self) -> Prop:
        return self.prop

    def toEvalAxiom(self) -> Proof:
        prop = ImplyProp(self, self.eval())
        return Proof(prop)

    def fromEvalAxiom(self) -> Proof:
        prop = ImplyProp(self.eval(), self)
        return Proof(prop)

    def __eq__(self, __o: Prop) -> bool:
        return self.eval() == __o.eval()


class AndProp(ExtProp):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        self.left_child = p1
        self.right_child = p2
        p = NotProp(ImplyProp(p1, NotProp(p2)))
        super().__init__(p)

    def __str__(self) -> str:
        return (
            "(" + self.left_child.__str__() + "/\\" + self.right_child.__str__() + ")"
        )


class OrProp(ExtProp):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        self.left_child = p1
        self.right_child = p2
        p = ImplyProp(NotProp(p1), p2)
        super().__init__(p)

    def __str__(self) -> str:
        return (
            "(" + self.left_child.__str__() + "\\/" + self.right_child.__str__() + ")"
        )


class IIFProp(ExtProp):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        self.left_child = p1
        self.right_child = p2
        p = NotProp(ImplyProp(p1, NotProp(p2)))
        p = AndProp(ImplyProp(p1, p2), ImplyProp(p2, p1))
        super().__init__(p.eval())

    def __str__(self) -> str:
        return (
            "(" + self.left_child.__str__() + "<=>" + self.right_child.__str__() + ")"
        )


class ExistProp(ExtProp):
    def __init__(self, x: Variable, p: Prop) -> None:
        self.variable = x
        self.child = p
        p = NotProp(ForallProp(x, NotProp(p)))
        super().__init__(p)

    def __str__(self) -> str:
        return "(exists " + self.variable.__str__() + "," + self.child.__str__() + ")"