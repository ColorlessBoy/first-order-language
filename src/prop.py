from __future__ import annotations

from variable import Variable


# BUG: 在 \forall 里，现在的alphaEq()有些问题，需要适用范围更广的alphaEq()。或者结合Axiom4也可以间接扩展alphaEq()
# TODO:
# 1. AndProp AndProof AndInverseProof
# 2. OrProp OrProof OrInverseProof
# 3. IIFProp IIFProof IIFInverseProof
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

    def getname(self) -> str:
        return self.__class__.__name__

    def alphaEq(
        self,
        other: Prop,
        self_var_to_int: dict[Variable, int],
        other_var_to_int: dict[Variable, int],
    ) -> bool:
        return self.getname() == other.getname()

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

    def alphaEq(
        self,
        other: VarProp,
        self_var_to_int: dict[Variable, int],
        other_var_to_int: dict[Variable, int],
    ) -> bool:
        return self.getname() == other.getname() and self.variable.alphaEq(
            other.variable, self_var_to_int, other_var_to_int
        )

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

    def alphaEq(
        self,
        other: NotProp,
        self_var_to_int: dict[Variable, int],
        other_var_to_int: dict[Variable, int],
    ) -> bool:
        return self.getname() == other.getname() and self.child.alphaEq(
            other.child, self_var_to_int, other_var_to_int
        )

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

    def alphaEq(
        self,
        other: ImplyProp,
        self_var_to_int: dict[Variable, int],
        other_var_to_int: dict[Variable, int],
    ) -> bool:
        return (
            self.getname() == other.getname()
            and self.left_child.alphaEq(
                other.left_child, self_var_to_int, other_var_to_int
            )
            and self.right_child.alphaEq(
                other.right_child, self_var_to_int, other_var_to_int
            )
        )

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
        self.freevars.remove(x)
        self.boundedvars.add(x)

    def substitute(self, x: Variable, y: Variable) -> ForallProp:
        if self.isfree(x) or self.isbounded(x):
            if self.variable == x:
                return ForallProp(y, self.child.substitute(x, y))
            return ForallProp(self.variable, self.child.substitute(x, y))
        return self

    def alphaEq(
        self,
        other: ForallProp,
        self_var_to_int: dict[Variable, int],
        other_var_to_int: dict[Variable, int],
    ) -> bool:
        return (
            self.getname() == other.getname()
            and self.variable.alphaEq(other.variable, self_var_to_int, other_var_to_int)
            and self.child.alphaEq(other.child, self_var_to_int, other_var_to_int)
        )

    def __eq__(self, __o: Prop) -> bool:
        __o2: ForallProp = __o  # type: ignore
        return (
            super().__eq__(__o)
            and self.variable == __o2.variable
            and self.child == __o2.child
        )

    def __str__(self) -> str:
        return "(forall " + self.variable.__str__() + "," + self.child.__str__() + ")"
