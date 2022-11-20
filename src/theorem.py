from __future__ import annotations

from extprop import ExistProp
from proof import (
    AlphaEqAxiom,
    Assumption,
    Axiom1,
    Axiom2,
    Axiom3,
    Axiom4,
    Axiom5,
    Generalization,
    ModusPonens,
    Proof,
)
from prop import ForallProp, ImplyProp, NotProp, Prop
from variable import Variable


class Theorem:
    def __init__(self, proof: Proof) -> None:
        self.proof = proof

    def getname(self) -> str:
        return self.__class__.__name__


class Reflexive(Theorem):
    def __init__(self, p: Prop) -> None:
        """Reflexive

        Args:
            p (Prop): any prop

        Returns:
            Proof: p => p
        """
        p2p = ImplyProp(p, p)
        proof1 = Axiom1(p, p)
        proof2 = Axiom1(p, p2p)
        proof3 = Axiom2(p, p2p, p)
        proof4 = ModusPonens(proof2, proof3)
        proof5 = ModusPonens(proof1, proof4)

        self.input = {"prop1": p}
        super().__init__(proof5)

    def __str__(self) -> str:
        return f"{self.getname()}[{self.input['prop1']}]"


class Transitive(Theorem):
    def __init__(self, proof1: Proof, proof2: Proof) -> None:
        """Transitive

        Args:
            proof1 (Proof): a => b
            proof2 (Proof): b => c

        Returns:
            Proof: a => c
        """
        if proof1.prop.getname() != "ImplyProp":
            raise ValueError("transitive(): proof1.prop should be an ImplyProp")
        if proof2.prop.getname() != "ImplyProp":
            raise ValueError("transitive(): proof2.prop should be an ImplyProp")
        p1: ImplyProp = proof1.prop  # type: ignore
        p2: ImplyProp = proof2.prop  # type: ignore
        if p1.right_child != p2.left_child:
            raise ValueError(
                "transitive(): proof1.prop.right_child != proof2.prop.left_child"
            )

        a = p1.left_child
        b = p1.right_child
        c = p2.right_child

        proof3 = Axiom1(p2, a)
        proof4 = ModusPonens(proof2, proof3)
        proof5 = Axiom2(a, b, c)
        proof6 = ModusPonens(proof4, proof5)
        proof7 = ModusPonens(proof1, proof6)

        self.input = {
            "proof1": proof1,
            "proof2": proof2,
        }
        super().__init__(proof7)

    def __str__(self) -> str:
        return f"{self.getname()} ({self.input['proof1'].__str__()}, {self.input['proof2'].__str__()})"


class Deduction(Theorem):
    def __init__(self, assumption: Assumption, proof: Proof) -> None:
        """Deduction: remove assumption

        Assumption[a] |=> b ===> |=> h_imply(a, b)

        Args:
            assumption (Assumption): any assumption a
            proof (Proof): any proof b

        Returns:
            Proof: a => b
        """
        output = proof
        if assumption == proof:
            output = Reflexive(proof.prop).proof
        elif proof.getname() in [
            "Axiom1",
            "Axiom2",
            "Axiom3",
            "Axiom4",
            "Axiom5",
            "Assumption",
            "AlphaEqAxiom",
        ]:
            """proof is not based on assumption x"""
            output = ModusPonens(proof, Axiom1(proof.prop, assumption.prop))
        elif proof.getname() == "ModusPonens":
            proof2: ModusPonens = proof  # type: ignore
            proof3 = Deduction(assumption, proof2.input["proof1"]).proof
            proof4 = Deduction(assumption, proof2.input["proof2"]).proof
            proof5 = Axiom2(assumption.prop, proof2.input["proof1"].prop, proof2.prop)
            proof6 = ModusPonens(proof3, ModusPonens(proof4, proof5))
            output = proof6
        elif proof.getname() == "Generalization":
            proof1: Generalization = proof  # type: ignore
            proof3 = Deduction(assumption, proof1.input["proof1"]).proof
            proof4 = Generalization(proof3, proof1.input["var1"])
            prop3: ImplyProp = proof3.prop  # type: ignore
            prop4 = prop3.left_child
            prop5 = prop3.right_child
            var = proof1.input["var1"]
            proof5 = Axiom5(prop4, prop5, var)
            proof6 = ModusPonens(proof4, proof5)
            output = proof6
        else:
            raise ValueError("Deduction(): Unknown kinds of proof.")

        self.input = {"proof1": assumption, "proof2": proof}
        super().__init__(output)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['proof1'].__str__()}, {self.input['proof2'].__str__()})"


class Exchange(Theorem):
    def __init__(self, proof: Proof) -> None:
        """Exchange

        Args:
            p (Prop): a => (b => c)

        Returns:
            Proof: b => (a => c)
        """
        if proof.prop.getname() != "ImplyProp":
            raise ValueError("Require p: a => (b => c)")
        p2: ImplyProp = proof.prop  # type: ignore
        if p2.right_child.getname() != "ImplyProp":
            raise ValueError("Require p: a => (b => c)")
        a: Prop = p2.left_child
        p3: ImplyProp = p2.right_child  # type: ignore
        b: Prop = p3.left_child
        c: Prop = p3.right_child

        s1 = Axiom1(b, a)  # b => (a => b)
        s2 = Axiom2(a, b, c)  # ((a => b)=>c) => ((a => b) => (a => c))
        s3 = ModusPonens(proof, s2)  # (a => b) => (a => c)
        s4 = Transitive(s1, s3)  # b => (a => c)
        super().__init__(s4.proof)


class FromDoubleNot(Theorem):
    def __init__(self, p: Prop) -> None:
        """!!p => p

        Args:
            p (Prop): _description_
        """
        proof1 = Axiom3(p, NotProp(p))  # (!p => !!p) => ((!p => !p) => p)
        theorem1 = Exchange(proof1)  # (!p => !p) => ((!p => !!p) => p)
        theorem2 = Reflexive(NotProp(p))  # !p => !p
        proof2 = ModusPonens(theorem2.proof, theorem1.proof)  # (!p => !!p) => p
        proof3 = Axiom1(NotProp(NotProp(p)), NotProp(p))  # !!p => (!p => !!p)
        theorem4 = Transitive(proof3, proof2)  # !!p => p
        super().__init__(theorem4.proof)


class ToDoubleNot(Theorem):
    def __init__(self, p: Prop) -> None:
        """p => !!p

        Args:
            p (Prop): _description_
        """
        proof1 = Axiom3(NotProp(NotProp(p)), p)  # (!!!p => !p) => ((!!!p => p) => !!p)
        theorem1 = FromDoubleNot(NotProp(p))  # !!!p => !p
        proof2 = ModusPonens(theorem1.proof, proof1)  # (!!!p => p) => !!p
        proof3 = Axiom1(p, NotProp(NotProp(NotProp(p))))  # p => (!!!p => p)
        theorem2 = Transitive(proof3, proof2)  # p => !!p
        super().__init__(theorem2.proof)


class FromInverseNotNot(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """(!p1 => !p2) => (p2 => p1)

        Args:
            proof (Proof): _description_
        """
        proof1 = Axiom1(p2, NotProp(p1))  # p2 => !p1 => p2
        proof2 = Axiom3(p1, p2)  # (!p1 => !p2) => ((!p1 => p2) => p1)
        theorem1 = Exchange(proof2)  # (!p1 => p2) => ((!p1 => !p2) => p1)
        theorem2 = Transitive(proof1, theorem1.proof)  # p2 => ((!p1 => !p2) => p1)
        theorem3 = Exchange(theorem2.proof)  # (!p1 => !p2) => p2 => p1
        super().__init__(theorem3.proof)


class ToInverseNotNot(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """(p1 => p2) => (!p2 => !p1)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        assume1 = Assumption(ImplyProp(p1, p2))  # p1 => p2
        theorem1 = FromDoubleNot(p1)  # !!p1 => p1
        theorem2 = Transitive(theorem1.proof, assume1)  # !!p1 => p2
        theorem3 = ToDoubleNot(p2)  # p2 => !!p2
        theorem4 = Transitive(theorem2.proof, theorem3.proof)  # !!p1 => !!p2
        theorem5 = FromInverseNotNot(
            NotProp(p1), NotProp(p2)
        )  # (!!p1 => !!p2) => (!p2 => !p1)
        proof1 = ModusPonens(theorem4.proof, theorem5.proof)  # !p2 => !p1
        theorem6 = Deduction(assume1, proof1)  # (p1 => p2) => (!p2 => !p1)
        super().__init__(theorem6.proof)


class Contradiction(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """(a => b) => (!a => b) => b

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        theorem1 = ToInverseNotNot(p1, p2)  # (p1 => p2) => (!p2 => !p1)
        theorem2 = ToInverseNotNot(NotProp(p1), p2)  # (!p1 => p2) => (!p2 => !!p1)
        proof1 = Axiom3(p2, NotProp(p1))  # (!p2 => !!p1) => (!p2 => !p1) => p2
        theorem3 = Transitive(
            theorem2.proof, proof1
        )  # (!p1 => p2) => (!p2 => !p1) => p2
        theorem4 = Exchange(theorem3.proof)  # (!p2 => !p1) => (!p1 => p2) => p2
        theorem5 = Transitive(
            theorem1.proof, theorem4.proof
        )  # (p1 => p2) => (!p1 => p2) => p2
        super().__init__(theorem5.proof)


class ExistentialRule(Theorem):
    def __init__(self, prop: Prop, x: Variable, y: Variable) -> None:
        proof1 = Axiom4(NotProp(prop), x, y)  # (forall x, !prop) => !prop[x => y]
        prop1: ImplyProp = proof1.prop  # type: ignore
        proof2 = ToInverseNotNot(prop1.left_child, prop1.right_child).proof
        proof3 = ModusPonens(proof1, proof2)  # !!prop[x => y] => !(forall x, !prop)
        prop5: NotProp = prop1.right_child  # type: ignore
        proof4 = ToDoubleNot(prop5.child).proof  # prop[x => y] => !!prop[x => y]
        proof5 = Transitive(proof4, proof3).proof  # prop[x => y] => !(forall x, !prop)

        prop2: ImplyProp = proof5.prop  # type:ignore
        prop3 = prop2.right_child
        prop4 = ExistProp(x, prop)
        proof6 = AlphaEqAxiom(prop3, prop4)

        proof7 = Transitive(proof5, proof6).proof

        super().__init__(proof7)
