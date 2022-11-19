from __future__ import annotations

from proof import (
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
from prop import ImplyProp, Prop


class Theorem(Proof):
    def __init__(self, proof: Proof) -> None:
        super().__init__(proof.prop)
        self.proof = proof


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
        elif assumption not in proof.assumption:
            """proof is not based on assumption x"""
            output = ModusPonens(proof, Axiom1(proof.prop, assumption.prop))
        elif proof.getname() == "Generalization":
            proof1: Generalization = proof  # type: ignore
            proof3 = Deduction(assumption, proof1.input["proof1"]).proof
            output = Generalization(proof3, proof1.input["var1"])
        elif proof.getname() == "ModusPonens":
            proof2: ModusPonens = proof  # type: ignore
            proof3 = Deduction(assumption, proof2.input["proof1"]).proof
            proof4 = Deduction(assumption, proof2.input["proof2"]).proof
            proof5 = Axiom2(assumption.prop, proof2.input["proof1"].prop, proof2.prop)
            proof6 = ModusPonens(proof3, ModusPonens(proof4, proof5))
            output = proof6
        else:
            raise ValueError("Deduction(): Unknown kinds of proof.")

        self.input = {"proof1": assumption, "proof2": proof}
        super().__init__(output)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['proof1'].__str__()}, {self.input['proof2'].__str__()})"
