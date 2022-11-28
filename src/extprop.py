from __future__ import annotations

from proof import Proof
from prop import ForallProp, ImplyProp, NotProp, Prop, Variable


class ExtProp(Prop):
    def __init__(self, p: Prop) -> None:
        super().__init__()
        self.prop = p

    def eval(self) -> Prop:
        return self.prop.eval()

    def __eq__(self, __o: Prop) -> bool:
        return self.eval() == __o.eval()


class ToEvalAxiom(Proof):
    def __init__(self, p: Prop) -> None:
        prop = ImplyProp(p, p.eval())
        self.input = {"prop": prop}
        super().__init__(prop)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop']})"


class FromEvalAxiom(Proof):
    def __init__(self, p: Prop) -> None:
        prop = ImplyProp(p.eval(), p)
        self.input = {"prop": prop}
        super().__init__(prop)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop']})"


class AndProp(ExtProp):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """AndProp

        Args:
            p1 (Prop): any prop
            p2 (Prop): any prop

        Returns:
            !(p1 => !p2)
        """
        self.left_child = p1
        self.right_child = p2
        p = NotProp(ImplyProp(p1, NotProp(p2)))
        super().__init__(p)

    def substitute(self, x: Variable, y: Variable) -> AndProp:
        if self.isfree(x) or self.isbounded(x):
            return AndProp(
                self.left_child.substitute(x, y), self.right_child.substitute(x, y)
            )
        return self

    def replacement(self, p1: Prop, p2: Prop) -> Prop:
        if self == p1:
            return p2
        return AndProp(
            self.left_child.replacement(p1, p2), self.right_child.replacement(p1, p2)
        )

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

    def substitute(self, x: Variable, y: Variable) -> OrProp:
        if self.isfree(x) or self.isbounded(x):
            return OrProp(
                self.left_child.substitute(x, y), self.right_child.substitute(x, y)
            )
        return self

    def replacement(self, p1: Prop, p2: Prop) -> Prop:
        if self == p1:
            return p2
        return OrProp(
            self.left_child.replacement(p1, p2), self.right_child.replacement(p1, p2)
        )

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
        super().__init__(p)

    def substitute(self, x: Variable, y: Variable) -> IIFProp:
        if self.isfree(x) or self.isbounded(x):
            return IIFProp(
                self.left_child.substitute(x, y), self.right_child.substitute(x, y)
            )
        return self

    def replacement(self, p1: Prop, p2: Prop) -> Prop:
        if self == p1:
            return p2
        return IIFProp(
            self.left_child.replacement(p1, p2), self.right_child.replacement(p1, p2)
        )

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

    def substitute(self, x: Variable, y: Variable) -> ExistProp:
        if self.isfree(x) or self.isbounded(x):
            if self.variable == x:
                return ExistProp(y, self.child.substitute(x, y))
            return ExistProp(self.variable, self.child.substitute(x, y))
        return self

    def replacement(self, p1: Prop, p2: Prop) -> Prop:
        if self == p1:
            return p2
        return ExistProp(self.variable, self.child.replacement(p1, p2))

    def __str__(self) -> str:
        return "(exists " + self.variable.__str__() + "," + self.child.__str__() + ")"
