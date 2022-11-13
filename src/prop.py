from __future__ import annotations

import copy

from variable import Variable


class Prop:
    def __init__(self, name: str) -> None:
        self.name = name
        self.freevars = set()
        self.boundedvars = set()

    def isfree(self, x: Variable) -> bool:
        return x in self.freevars

    def isbounded(self, x: Variable) -> bool:
        return x in self.boundedvars

    def substitute(self, x: Variable, y: Variable) -> Prop:
        return copy.deepcopy(self)

    def __eq__(self, p: Prop) -> bool:
        return self.name == p.name


class VarProp(Prop):
    def __init__(self, x: Variable) -> None:
        super().__init__("VarProp")
        self.variable = x
        self.freevars.add(x)

    def substitute(self, x: Variable, y: Variable) -> VarProp:
        if self.variable == x:
            return VarProp(y)
        return self

    def __eq__(self, p: VarProp) -> bool:
        return self.name == p.name and self.variable == p.variable

    def __str__(self) -> str:
        return self.variable.__str__()


class NotProp(Prop):
    def __init__(self, p: Prop) -> None:
        super().__init__("NotProp")
        self.child = p
        self.freevars = p.freevars.copy()
        self.boundedvars = p.boundedvars.copy()

    def substitute(self, x: Variable, y: Variable) -> NotProp:
        if self.isfree(x) or self.isbounded(x):
            return NotProp(self.child.substitute(x, y))
        return self

    def __eq__(self, p: NotProp) -> bool:
        return self.name == p.name and self.child == p.child

    def __str__(self) -> str:
        return "!(" + self.child.__str__() + ")"


class ImplyProp(Prop):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        super().__init__("ImplyProp")
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

    def __eq__(self, p: ImplyProp) -> bool:
        return (
            self.name == p.name
            and self.left_child == p.left_child
            and self.right_child == p.right_child
        )

    def __str__(self) -> str:
        return "(" + self.left_child.__str__() + "=>" + self.right_child.__str__() + ")"


class ForallProp(Prop):
    def __init__(self, x: Variable, p: Prop) -> None:
        super().__init__("ForallProp")
        self.variable = x
        self.child = p
        self.freevars = p.freevars.copy()
        self.boundedvars = p.boundedvars.copy()
        self.freevars.remove(x)
        self.boundedvars.add(x)

    def substitute(self, x: Variable, y: Variable) -> ForallProp:
        if self.isfree(x) or self.isbounded(x):
            if self.variable == x:
                return ForallProp(y, self.child.substitute(x, y))
            return ForallProp(self.variable, self.child.substitute(x, y))
        return self

    def __eq__(self, p: ForallProp) -> bool:
        return (
            self.name == p.name
            and self.variable == p.variable
            and self.child == p.child
        )

    def __str__(self) -> str:
        return "(\forall" + self.variable.__str__() + "," + self.child.__str__() + ")"
