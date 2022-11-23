from __future__ import annotations

from prop import ForallProp, ImplyProp, NotProp, Prop
from variable import Variable


# BUG: assumption不一样的Proof是否应该相等呢？
# BUG: 现在的代码没有突出Deduction的意义，即消除assumption。
class Proof:
    def __init__(self, p: Prop) -> None:
        self.prop = p
        self.assumption = []

    def getname(self) -> str:
        return self.__class__.__name__

    def eval(self) -> Proof:
        return Proof(self.prop)

    def alphaEq(self, proof: Proof) -> bool:
        return self.prop.alphaEq(proof.prop, {}, {})

    def __eq__(self, __o: Proof) -> bool:
        return self.prop == __o.prop

    def __str__(self) -> str:
        return self.getname() + "[" + self.prop.__str__() + "]"


class Assumption(Proof):
    def __init__(self, p: Prop):
        super().__init__(p)
        self.assumption = [self]


class Axiom1(Proof):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """Axiom1

        Args:
            p1 (Prop): any prop
            p2 (Prop): any prop

        Returns:
            Proof: p1 => (p2 => p1)
        """
        self.input = {"prop1": p1, "prop2": p2}
        self.prop = ImplyProp(p1, ImplyProp(p2, p1))
        self.assumption = []

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class Axiom2(Proof):
    def __init__(self, p1: Prop, p2: Prop, p3: Prop) -> None:
        """Axiom2

        Args:
            p1 (Prop): any prop
            p2 (Prop): any prop
            p3 (Prop): any prop

        Returns:
            Proof: (p1 => (p2 => p3)) => ((p1 => p2) => (p1 => p3))
        """
        self.input = {"prop1": p1, "prop2": p2, "prop3": p3}
        p4 = ImplyProp(p1, ImplyProp(p2, p3))
        p5 = ImplyProp(ImplyProp(p1, p2), ImplyProp(p1, p3))
        p6 = ImplyProp(p4, p5)
        self.prop = p6
        self.assumption = []

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()}, {self.input.__str__()})"


class Axiom3(Proof):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """Axiom3

        Args:
            p1 (Prop): any prop
            p2 (Prop): any prop

        Returns:
            Proof: (!p1 => !p2) => ((!p1 => p2) => p1)
        """
        self.input = {"prop1": p1, "prop2": p2}
        p3 = ImplyProp(NotProp(p1), NotProp(p2))
        p4 = ImplyProp(NotProp(p1), p2)
        p5 = ImplyProp(p3, ImplyProp(p4, p1))
        self.prop = p5
        self.assumption = []

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class ForallElimAxiom(Proof):
    def __init__(self, p: Prop, x: Variable) -> None:
        """(forall x, p) => p

        Args:
            p (Prop): any prop
            x (Variable): x should be not bounded in p
        """
        p1 = ForallProp(x, p)
        p3 = ImplyProp(p1, p)
        self.input = {"prop1": p, "var1": x}
        super().__init__(p3)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['var1'].__str__()})"


class ForallIntroAxiom(Proof):
    def __init__(self, p: Prop, x: Variable) -> None:
        """p => (forall x, p)

        Args:
            p (Prop): any prop
            x (Variable): x should be not bounded in p
        """
        p1 = ForallProp(x, p)
        p3 = ImplyProp(p, p1)
        self.input = {"prop1": p, "var1": x}
        super().__init__(p3)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['var1'].__str__()})"


class ForallImplyExchangeAxiom(Proof):
    def __init__(self, p1: Prop, p2: Prop, x: Variable) -> None:
        """Axiom5

        Args:
            p1 (Prop): any prop
            p2 (Prop): any prop
            x (Variable): x should not be free in p1

        Raises:
            ValueError: Axiom5(): x should not be free in p1

        Returns:
            Proof: (\forall x, p1 => p2) => (p1 => \forall p2)
        """
        if p1.isfree(x):
            raise ValueError("Axiom5(): x should not be free in p1")
        p3 = ForallProp(x, ImplyProp(p1, p2))
        p4 = ImplyProp(p1, ForallProp(x, p2))
        p5 = ImplyProp(p3, p4)

        self.input = {"prop1": p1, "prop2": p2, "var1": x}
        super().__init__(p5)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()}, {self.input['var1'].__str__()})"


class RenameAxiom(Proof):
    def __init__(self, p: Prop, x: Variable, y: Variable) -> None:
        if p.isbounded(x):
            raise ValueError("RenameAxiom(): x should not be bounded in p")
        if p.isbounded(y):
            raise ValueError("RenameAxiom(): y should not be bounded in p")
        if x != y:
            p2 = p.substitute(x, y)
        else:
            p2 = p
        p3 = ImplyProp(p, p2)

        self.input = {"prop1": p, "var1": x, "var2": y}
        super().__init__(p3)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['var1'].__str__()}, {self.input['var2'].__str__()})"


class ModusPonens(Proof):
    def __init__(self, proof1: Proof, proof2: Proof) -> None:
        """Modus Ponens

        Args:
            proof1 (Proof): proof(a)
            proof2 (Proof): proof(a => b)

        Raises:
            ValueError: ModusPonens(): proof2.prop should be an ImplyProp
            ValueError: ModusPonens(): proof1 != proof2.prop.left_child

        Returns:
            Proof: proof(b)
        """
        if proof2.prop.getname() != "ImplyProp":
            raise ValueError("ModusPonens(): proof2.prop should be an ImplyProp")
        p: ImplyProp = proof2.prop  # type: ignore
        if proof1.prop != p.left_child:
            raise ValueError("ModusPonens(): proof1.prop != proof2.prop.left_child")
        self.input = {"proof1": proof1, "proof2": proof2}
        self.prop = p.right_child
        self.assumption = proof1.assumption + proof2.assumption

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['proof1'].__str__()}, {self.input['proof2'].__str__()})"
