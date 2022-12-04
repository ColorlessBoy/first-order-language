from __future__ import annotations

from variable import Variable


class Prop:
    def __init__(self) -> None:
        self.freevars = set()
        self.boundedvars = set()

    def isfree(self, x: Variable) -> bool:
        return x in self.freevars

    def isbounded(self, x: Variable) -> bool:
        return x in self.boundedvars

    def substitute(self, x: Variable, y: Variable) -> Prop:
        return self

    def replacement(self, p1: Prop, p2: Prop) -> Prop:
        return self

    def getname(self) -> str:
        return self.__class__.__name__

    def eval(self) -> Prop:
        return self

    def __eq__(self, __o: Prop) -> bool:
        return self.getname() == __o.getname()

    def __str__(self) -> str:
        return f"{self.getname()}()"


class VarProp(Prop):
    def __init__(self, x: Variable) -> None:
        super().__init__()
        self.variable = x
        self.freevars.add(x)

    def substitute(self, x: Variable, y: Variable) -> VarProp:
        if self.variable == x:
            return VarProp(y)
        return self

    def replacement(self, p1: Prop, p2: Prop) -> Prop:
        if self == p1:
            return p2
        return self

    def eval(self) -> Prop:
        return self

    def __eq__(self, __o: Prop) -> bool:
        __o2: VarProp = __o  # type: ignore
        return super().__eq__(__o) and self.variable == __o2.variable

    def __str__(self) -> str:
        return self.variable.__str__()


class NotProp(Prop):
    def __init__(self, p: Prop) -> None:
        super().__init__()
        self.child = p
        self.freevars = p.freevars.copy()
        self.boundedvars = p.boundedvars.copy()

    def substitute(self, x: Variable, y: Variable) -> NotProp:
        if self.isfree(x) or self.isbounded(x):
            return NotProp(self.child.substitute(x, y))
        return self

    def replacement(self, p1: Prop, p2: Prop) -> Prop:
        if self == p1:
            return p2
        return NotProp(self.child.replacement(p1, p2))

    def eval(self) -> Prop:
        return NotProp(self.child.eval())

    def __eq__(self, __o: Prop) -> bool:
        __o2: NotProp = __o  # type: ignore
        return super().__eq__(__o) and self.child == __o2.child

    def __str__(self) -> str:
        return "!" + self.child.__str__()


class ImplyProp(Prop):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        super().__init__()
        self.left_child = p1
        self.right_child = p2
        self.freevars = set.union(p1.freevars, p2.freevars)
        self.boundedvars = set.union(p1.boundedvars, p2.boundedvars)

    def substitute(self, x: Variable, y: Variable) -> ImplyProp:
        if self.isfree(x) or self.isbounded(x):
            return ImplyProp(
                self.left_child.substitute(x, y), self.right_child.substitute(x, y)
            )
        return self

    def replacement(self, p1: Prop, p2: Prop) -> Prop:
        if self == p1:
            return p2
        return ImplyProp(
            self.left_child.replacement(p1, p2), self.right_child.replacement(p1, p2)
        )

    def eval(self) -> Prop:
        return ImplyProp(self.left_child.eval(), self.right_child.eval())

    def __eq__(self, __o: Prop) -> bool:
        __o2: ImplyProp = __o  # type: ignore
        return (
            super().__eq__(__o)
            and self.left_child == __o2.left_child
            and self.right_child == __o2.right_child
        )

    def __str__(self) -> str:
        return "(" + self.left_child.__str__() + "=>" + self.right_child.__str__() + ")"


class ForallProp(Prop):
    def __init__(self, x: Variable, p: Prop) -> None:
        super().__init__()
        self.variable = x
        self.child = p
        self.freevars = p.freevars.copy()
        self.boundedvars = p.boundedvars.copy()
        if x in self.freevars:
            self.freevars.remove(x)
        self.boundedvars.add(x)

    def substitute(self, x: Variable, y: Variable) -> ForallProp:
        if self.isfree(x) or self.isbounded(x):
            if self.variable == x:
                return ForallProp(y, self.child.substitute(x, y))
            return ForallProp(self.variable, self.child.substitute(x, y))
        return self

    def replacement(self, p1: Prop, p2: Prop) -> Prop:
        if self == p1:
            return p2
        return ForallProp(self.variable, self.child.replacement(p1, p2))

    def eval(self) -> Prop:
        return ForallProp(self.variable, self.child.eval())

    def __eq__(self, __o: Prop) -> bool:
        __o2: ForallProp = __o  # type: ignore
        return (
            super().__eq__(__o)
            and self.variable == __o2.variable
            and self.child == __o2.child
        )

    def __str__(self) -> str:
        return "(forall " + self.variable.__str__() + "," + self.child.__str__() + ")"


class AliasProp(Prop):
    def __init__(self, p: Prop) -> None:
        super().__init__()
        self.prop = p
        self.freevars = p.freevars
        self.boundedvars = p.boundedvars

    def eval(self) -> Prop:
        return self.prop.eval()

    def __eq__(self, __o: Prop) -> bool:
        return self.eval() == __o.eval()


class AndProp(AliasProp):
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


class OrProp(AliasProp):
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


class IIFProp(AliasProp):
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


class ExistProp(AliasProp):
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
