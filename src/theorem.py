from __future__ import annotations

from extprop import AndProp, ExistProp, FromEvalAxiom, IIFProp, OrProp, ToEvalAxiom
from proof import (
    Assumption,
    Axiom1,
    Axiom2,
    Axiom3,
    ForallElimAxiom,
    ForallImplyExchangeAxiom,
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
    def __init__(self, assume: Assumption, proof: Proof) -> None:
        """Deduction: remove assumption (Not in Generalization)

        Assumption[a] |=> b ===> |=> h_imply(a, b)

        Raise:
            "Deduction(): x which in Gen(..., x) should not be free in assume."

        Args:
            assumption (Assumption): any assumption a
            proof (Proof): any proof b

        Returns:
            Proof: a => b
        """
        output = proof
        # if assume == proof:
        #     output = Reflexive(assume.prop).proof
        if proof.getname() == "Assumption" and assume == proof:
            output = Reflexive(proof.prop).proof
        elif (
            proof.getname()
            in [
                "Axiom1",
                "Axiom2",
                "Axiom3",
                "ForallElimAxiom",
                "ForallImplyExchangeAxiom",
                "Assumption",
                "ToEvalAxiom",
                "FromEvalAxiom",
            ]
            or assume not in proof.assumption
        ):
            """proof is not based on assumption x"""
            output = ModusPonens(proof, Axiom1(proof.prop, assume.prop))
        elif proof.getname() == "Generalization":
            g_proof1: Generalization = proof  # type: ignore
            g_proof2 = g_proof1.input["proof1"]
            g_x = g_proof1.input["var1"]
            if assume.prop.isfree(g_x):
                raise ValueError(
                    "Deduction(): x which in Gen(..., x) should not be free in assume."
                )
            g_proof4 = Deduction(assume, g_proof2).proof  # assume.prop => g_proof2.prop
            g_proof5 = ForallImplyExchangeAxiom(
                assume.prop, g_proof2.prop, g_x
            )  # (forall x, assume.prop => g_proof2.prop) => (assume.prop => (forall x, g_proof2.prop))
            g_proof6 = Generalization(
                g_proof4, g_x
            )  # (forall x, assume.prop => g_proof2.prop)
            g_proof7 = ModusPonens(
                g_proof6, g_proof5
            )  # (assume.prop => (forall x, g_proof2.prop))
            output = g_proof7
        elif proof.getname() == "ModusPonens":
            proof2: ModusPonens = proof  # type: ignore
            proof3 = Deduction(assume, proof2.input["proof1"]).proof
            proof4 = Deduction(assume, proof2.input["proof2"]).proof
            proof5 = Axiom2(assume.prop, proof2.input["proof1"].prop, proof2.prop)
            proof6 = ModusPonens(proof4, proof5)
            proof7 = ModusPonens(proof3, proof6)
            output = proof7
        else:
            raise ValueError("Deduction(): Unknown kinds of proof.")

        self.input = {"proof1": assume, "proof2": proof}
        super().__init__(output)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['proof1'].__str__()}, {self.input['proof2'].__str__()})"


class ImplyExchange(Theorem):
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

        self.input = {"proof1": proof}
        super().__init__(s4.proof)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['proof1'].__str__()})"


class DoubleNotElim(Theorem):
    def __init__(self, p: Prop) -> None:
        """!!p => p

        Args:
            p (Prop): _description_
        """
        proof1 = Axiom3(p, NotProp(p))  # (!p => !!p) => ((!p => !p) => p)
        theorem1 = ImplyExchange(proof1)  # (!p => !p) => ((!p => !!p) => p)
        theorem2 = Reflexive(NotProp(p))  # !p => !p
        proof2 = ModusPonens(theorem2.proof, theorem1.proof)  # (!p => !!p) => p
        proof3 = Axiom1(NotProp(NotProp(p)), NotProp(p))  # !!p => (!p => !!p)
        theorem4 = Transitive(proof3, proof2)  # !!p => p

        self.input = {"prop1": p}
        super().__init__(theorem4.proof)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()})"


class DoubleNotIntro(Theorem):
    def __init__(self, p: Prop) -> None:
        """p => !!p

        Args:
            p (Prop): _description_
        """
        proof1 = Axiom3(NotProp(NotProp(p)), p)  # (!!!p => !p) => ((!!!p => p) => !!p)
        theorem1 = DoubleNotElim(NotProp(p))  # !!!p => !p
        proof2 = ModusPonens(theorem1.proof, proof1)  # (!!!p => p) => !!p
        proof3 = Axiom1(p, NotProp(NotProp(NotProp(p))))  # p => (!!!p => p)
        theorem2 = Transitive(proof3, proof2)  # p => !!p

        self.input = {"prop1": p}
        super().__init__(theorem2.proof)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()})"


class NotToNotElim(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """(!p1 => !p2) => (p2 => p1)

        Args:
            proof (Proof): _description_
        """
        proof1 = Axiom1(p2, NotProp(p1))  # p2 => !p1 => p2
        proof2 = Axiom3(p1, p2)  # (!p1 => !p2) => ((!p1 => p2) => p1)
        theorem1 = ImplyExchange(proof2)  # (!p1 => p2) => ((!p1 => !p2) => p1)
        theorem2 = Transitive(proof1, theorem1.proof)  # p2 => ((!p1 => !p2) => p1)
        theorem3 = ImplyExchange(theorem2.proof)  # (!p1 => !p2) => p2 => p1

        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(theorem3.proof)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class NotToNotIntro(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """(p1 => p2) => (!p2 => !p1)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        assume1 = Assumption(ImplyProp(p1, p2))  # p1 => p2
        theorem1 = DoubleNotElim(p1)  # !!p1 => p1
        theorem2 = Transitive(theorem1.proof, assume1)  # !!p1 => p2
        theorem3 = DoubleNotIntro(p2)  # p2 => !!p2
        theorem4 = Transitive(theorem2.proof, theorem3.proof)  # !!p1 => !!p2
        theorem5 = NotToNotElim(
            NotProp(p1), NotProp(p2)
        )  # (!!p1 => !!p2) => (!p2 => !p1)
        proof1 = ModusPonens(theorem4.proof, theorem5.proof)  # !p2 => !p1
        theorem6 = Deduction(assume1, proof1)  # (p1 => p2) => (!p2 => !p1)

        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(theorem6.proof)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class Contradiction(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """(a => b) => (!a => b) => b

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        theorem1 = NotToNotIntro(p1, p2)  # (p1 => p2) => (!p2 => !p1)
        theorem2 = NotToNotIntro(NotProp(p1), p2)  # (!p1 => p2) => (!p2 => !!p1)
        proof1 = Axiom3(p2, NotProp(p1))  # (!p2 => !!p1) => (!p2 => !p1) => p2
        theorem3 = Transitive(
            theorem2.proof, proof1
        )  # (!p1 => p2) => (!p2 => !p1) => p2
        theorem4 = ImplyExchange(theorem3.proof)  # (!p2 => !p1) => (!p1 => p2) => p2
        theorem5 = Transitive(
            theorem1.proof, theorem4.proof
        )  # (p1 => p2) => (!p1 => p2) => p2

        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(theorem5.proof)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class ImplyNotExchange(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """(p1 => !p2) => (p2 => !p1)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        proof1 = NotToNotElim(NotProp(p1), p2).proof  # (!!p1 => !p2) => (p2 => !p1)
        proof2 = DoubleNotElim(p1).proof  # !!p1 => p1
        assume1 = Assumption(ImplyProp(p1, NotProp(p2)))  # p1 => !p2
        proof3 = Transitive(proof2, assume1).proof  # !!p1 => !p2
        proof4 = ModusPonens(proof3, proof1)  # p2 => !p1
        proof5 = Deduction(assume1, proof4).proof  # (p1 => !p2) => (p2 => !p1)

        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(proof5)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class NotImplyExchange(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """(!p1 => p2) => (!p2 => p1)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        proof1 = NotToNotIntro(NotProp(p1), p2).proof  # (!p1 => p2) => (!p2 => !!p1)
        assume1 = Assumption(ImplyProp(NotProp(p1), p2))
        proof2 = ModusPonens(assume1, proof1)  # !p2 => !!p1
        proof3 = DoubleNotElim(p1).proof  # !!p1 => p1
        proof4 = Transitive(proof2, proof3).proof  # !p2 => p1
        proof5 = Deduction(assume1, proof4).proof  # (!p1 => p2) => (!p2 => p1)

        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(proof5)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class NotImplyToLeft(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """!(p1 => p2) => p1

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        proof1 = Axiom1(NotProp(p1), NotProp(p2))  # !p1 => (!p2 => !p1)
        proof2 = NotToNotElim(p2, p1).proof  # (!p2 => !p1) => (p1 => p2)
        proof3 = Transitive(proof1, proof2).proof  # !p1 => (p1 => p2)
        proof4 = NotImplyExchange(
            p1, ImplyProp(p1, p2)
        ).proof  # (!p1 => (p1 => p2)) => (!(p1 => p2) => p1)
        proof5 = ModusPonens(proof3, proof4)  # !(p1 => p2) => p1
        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(proof5)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class NotImplyToNotRight(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """!(p1 => p2) => !p2

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        proof1 = Axiom1(p2, p1)  # p2 => (p1 => p2)
        proof2 = NotToNotIntro(
            p2, ImplyProp(p1, p2)
        ).proof  # (p2 => (p1 => p2)) => (!(p1 => p2) => !p2)
        proof3 = ModusPonens(proof1, proof2)  # !(p1 => p2) => !p2
        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(proof3)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class NotImplyIntro(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """p1 => !p2 => !(p1 => p2)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        proof1 = Reflexive(ImplyProp(p1, p2)).proof  # (p1 => p2) => (p1 => p2)
        proof2 = ImplyExchange(proof1).proof  # p1 => (p1 => p2) => p2
        proof3 = NotToNotIntro(
            ImplyProp(p1, p2), p2
        ).proof  # ((p1 => p2) => p2) => (!p2 => !(p1 => p2))
        proof4 = Transitive(proof2, proof3).proof  # p1 => (!p2 => !(p1 => p2))

        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(proof4)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class AndElim(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """p1 /\\ p2 => p2

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        proof3 = NotImplyToNotRight(p1, NotProp(p2)).proof  # (!(p1 => !p2) => !!p2)
        proof4 = DoubleNotElim(p2).proof  # !!p2 => p2
        proof5 = Transitive(proof3, proof4).proof  # (!(p1 => !p2) => p2)

        p3 = AndProp(p1, p2)
        proof6 = ToEvalAxiom(p3)
        proof7 = Transitive(proof6, proof5).proof  # (p1 /\\ p2) => p2

        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(proof7)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class AndIntro(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """p1 => p2 => p1 /\\ p2

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        assume1 = Assumption(p1)
        assume2 = Assumption(ImplyProp(p1, NotProp(p2)))  # p1 => !p2
        proof1 = ModusPonens(assume1, assume2)  # !p2
        proof2 = Deduction(assume2, proof1).proof  # (p1 => !p2) => !p2
        proof3 = NotToNotIntro(
            ImplyProp(p1, NotProp(p2)), NotProp(p2)
        ).proof  # ((p1 => !p2) => !p2) => !!p2 => !(p1 => !p2)
        proof4 = ModusPonens(proof2, proof3)  # !!p2 => !(p1 => !p2)
        proof5 = DoubleNotIntro(p2).proof  # p2 => !!p2
        proof6 = Transitive(proof5, proof4).proof  # p2 => !(p1 => !p2)
        prop6: ImplyProp = proof6.prop  # type: ignore
        proof61 = ToEvalAxiom(prop6.right_child)
        proof62 = Transitive(proof6, proof61).proof
        prop1 = AndProp(p1, p2)  # p1 /\\ p2
        proof7 = FromEvalAxiom(prop1)  # !(p1 => !p2) => p1 /\\ p2
        proof8 = Transitive(proof62, proof7).proof  # p2 => p1 /\\ p2
        proof9 = Deduction(assume1, proof8).proof  # p1 => (p2 => p1 /\\ p2)

        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(proof9)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class AndExchange(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """p1 /\\ p2 => p2 /\\ p1

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        proof5 = ImplyNotExchange(p2, p1).proof  # (p2 => !p1) => (p1 => !p2)
        proof6 = NotToNotIntro(
            ImplyProp(p2, NotProp(p1)), ImplyProp(p1, NotProp(p2))
        ).proof  # ((p2 => !p1) => (p1 => !p2)) => (!(p1 => !p2) => !(p2 => !p1))
        proof7 = ModusPonens(proof5, proof6)  # !(p1 => !p2) => !(p2 => !p1)
        prop1 = AndProp(p1, p2)
        prop2 = AndProp(p2, p1)
        proof8 = ToEvalAxiom(prop1)
        proof9 = FromEvalAxiom(prop2)
        proof10 = Transitive(proof8, proof7).proof  # And(p1, p2) => !(p2 => !p1)
        proof11 = Transitive(proof10, proof9).proof  # And(p1, p2) => And(p2, p1)

        self.input = {
            "prop1": p1,
            "prop2": p2,
        }
        super().__init__(proof11)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class OrElim(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """p1 \\/ p2 => !p1 => p2

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        prop1 = OrProp(p1, p2)
        proof4 = ToEvalAxiom(prop1)

        self.input = {
            "prop1": p1,
            "prop2": p2,
        }
        super().__init__(proof4)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class OrIntro(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """p2 => p1 \\/ p2

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        proof1 = Axiom1(p2, NotProp(p1))
        prop1 = OrProp(p1, p2)
        proof2 = FromEvalAxiom(prop1)
        proof3 = Transitive(proof1, proof2).proof

        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(proof3)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class OrExchange(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """p1 \\/ p2 => p2 \\/ p1

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        proof5 = NotImplyExchange(p1, p2).proof  # (!p1 => p2) => (!p2 => p1)

        prop1 = OrProp(p1, p2)
        prop2 = OrProp(p2, p1)
        proof6 = ToEvalAxiom(prop1)  # p1 /\\ p2 => (!p1 => p2)
        proof7 = FromEvalAxiom(prop2)  # (!p2 => p1) => p2 /\\ p1
        proof8 = Transitive(proof6, proof5).proof  # p1 /\\ p2 => (!p2 => p1)
        proof9 = Transitive(proof8, proof7).proof  # p1 /\\ p2 => p2 /\\ p1

        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(proof9)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class NotAndToOrNot(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """!(p1 /\\ p2) => (!p1 \\/ !p2)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        prop1 = NotProp(ImplyProp(p1, NotProp(p2)))  # !(p1 => !p2)
        prop2 = AndProp(p1, p2)
        proof1 = FromEvalAxiom(prop2)  # !(p1 => !p2) => (p1 /\\ p2)
        proof2 = NotToNotIntro(
            prop1, prop2
        ).proof  # (!(p1 => !p2) => (p1 /\\ p2)) => (!(p1 /\\ p2) => !!(p1 => !p2))
        proof3 = ModusPonens(proof1, proof2)  # !(p1 /\\ p2) => !!(p1 => !p2)
        prop2 = ImplyProp(p1, NotProp(p2))
        proof4 = DoubleNotElim(prop2).proof  # !!(p1 => !p2) => (p1 => !p2)
        proof5 = Transitive(proof3, proof4).proof  # !(p1 /\\ p2) => (p1 => !p2)
        proof6 = NotToNotIntro(p1, NotProp(p2)).proof  # (p1 => !p2) => (!!p2 => !p1)
        proof7 = Transitive(proof5, proof6).proof  # !(p1 /\\ p2) => (!!p2 => !p1)
        prop3 = OrProp(NotProp(p2), NotProp(p1))
        proof8 = FromEvalAxiom(prop3)  # (!!p2 => !p1) => (!p2 \\/ !p1)
        proof9 = Transitive(proof7, proof8).proof  # !(p1 /\\ p2) => (!p2 \\/ !p1)

        proof10 = OrExchange(
            NotProp(p2), NotProp(p1)
        ).proof  # (!p2 \\/ !p1) => (!p1 \\/ !p2)
        proof11 = Transitive(proof9, proof10).proof  # !(p1 /\\ p2) => (!p1 \\/ !p2)

        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(proof11)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class NotOrToAndNot(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """!(p1 \\/ p2) => (!p1 /\\ !p2)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        prop1 = ImplyProp(NotProp(p1), NotProp(NotProp(p2)))
        assume1 = Assumption(prop1)  # !p1 => !!p2
        proof1 = DoubleNotElim(p2).proof  # !!p2 => p2
        proof2 = Transitive(assume1, proof1).proof  # !p1 => p2
        proof3 = Deduction(assume1, proof2).proof  # (!p1 => !!p2) => (!p1 => p2)
        prop2 = OrProp(p1, p2)
        proof4 = FromEvalAxiom(prop2)  # (!p1 => p2) => (p1 \\/ p2)
        proof5 = Transitive(proof3, proof4).proof  # (!p1 => !!p2) => (p1 \\/ p2)

        proof6 = NotToNotIntro(
            prop1, prop2
        ).proof  # ((!p1 => !!p2) => (p1 \\/ p2)) => (!(p1 \\/ p2) => !(!p1 => !!p2))

        proof7 = ModusPonens(proof5, proof6)  # !(p1 \\/ p2) => !(!p1 => !!p2)

        prop3 = AndProp(NotProp(p1), NotProp(p2))
        proof8 = FromEvalAxiom(prop3)  # !(!p1 => !!p2) => (!p1 /\\ !p2)
        proof9 = Transitive(proof7, proof8).proof  # !(p1 \\/ p2) => (!p1 /\\ !p2)

        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(proof9)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class IIFElim(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """(p1 <=> p2) => (p1 => p2)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        prop1 = IIFProp(p1, p2)  # p1 <=> p2
        proof1 = ToEvalAxiom(prop1)  # p1 <=> p2 => (***)
        prop2 = AndProp(ImplyProp(p1, p2), ImplyProp(p2, p1))
        proof2 = FromEvalAxiom(prop2)
        proof3 = Transitive(
            proof1, proof2
        ).proof  # p1 <=> p2 => ((p1 => p2)/\\(p2 => p1))
        proof4 = AndExchange(ImplyProp(p1, p2), ImplyProp(p2, p1)).proof
        proof5 = Transitive(
            proof3, proof4
        ).proof  # p1 <=> p2 => ((p2 => p1)/\\(p1 => p2))
        proof6 = AndElim(ImplyProp(p2, p1), ImplyProp(p1, p2)).proof
        proof7 = Transitive(proof5, proof6).proof  # p1 <=> p2 => (p1 => p2)
        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(proof7)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class IIFIntro(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """(p1 => p2) => (p2 => p1) => (p1 <=> p2)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        prop1 = IIFProp(p1, p2)  # p1 <=> p2
        proof1 = FromEvalAxiom(prop1)  # (***) => p1 <=> p2
        prop2 = AndProp(ImplyProp(p1, p2), ImplyProp(p2, p1))
        proof2 = ToEvalAxiom(prop2)
        proof3 = Transitive(
            proof2, proof1
        ).proof  # ((p1 => p2)/\\(p2 => p1)) => (p1 <=> p2)
        proof4 = AndIntro(ImplyProp(p1, p2), ImplyProp(p2, p1)).proof
        assume1 = Assumption(ImplyProp(p1, p2))
        proof5 = ModusPonens(assume1, proof4)  # (p2 => p1) => ((p1 => p2)/\\(p2 => p1))
        proof6 = Transitive(proof5, proof3).proof  # (p2 => p1) => (p1 <=> p2)
        proof7 = Deduction(
            assume1, proof6
        ).proof  # (p1 => p2) => (p2 => p1) => (p1 <=> p2)
        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(proof7)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class IIFExchange(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """(p1 <=> p2) => (p2 <=> p1)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        prop1 = IIFProp(p1, p2)  # p1 <=> p2
        proof1 = ToEvalAxiom(prop1)  # p1 <=> p2 => (***)
        prop2 = AndProp(ImplyProp(p1, p2), ImplyProp(p2, p1))
        proof2 = FromEvalAxiom(prop2)
        proof3 = Transitive(
            proof1, proof2
        ).proof  # p1 <=> p2 => ((p1 => p2)/\\(p2 => p1))

        proof4 = AndExchange(ImplyProp(p1, p2), ImplyProp(p2, p1)).proof
        proof5 = Transitive(
            proof3, proof4
        ).proof  # p1 <=> p2 => ((p2 => p1)/\\(p1 => p2))
        prop3 = AndProp(ImplyProp(p2, p1), ImplyProp(p1, p2))
        proof6 = ToEvalAxiom(prop3)
        proof7 = Transitive(proof5, proof6).proof  # p1 <=> p2 => (***)

        prop4 = IIFProp(p2, p1)  # p2 <=> p1
        proof8 = FromEvalAxiom(prop4)  # (***) => (p2 <=> p1)

        proof9 = Transitive(proof7, proof8).proof  # (p1 <=> p2) => (p2 <=> p1)
        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(proof9)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class IIFToNotIIF(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """(p1 <=> p2) => (!p1 <=> !p2)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        prop1 = IIFProp(p1, p2)
        assume1 = Assumption(prop1)
        proof1 = IIFElim(p1, p2).proof  # (p1 <=> p2) => (p1 => p2)
        proof2 = ModusPonens(assume1, proof1)  # p1 => p2
        proof3 = IIFElim(p2, p1).proof  # (p2 <=> p1) => (p2 => p1)
        proof4 = IIFExchange(p1, p2).proof  # (p1 <=> p2) => (p2 <=> p1)
        proof5 = Transitive(proof4, proof3).proof  # (p1 <=> p2) => (p2 => p1)
        proof6 = ModusPonens(assume1, proof5)  # p2 => p1

        proof7 = NotToNotIntro(p1, p2).proof  # (p1 => p2) => (!p2 => !p1)
        proof8 = ModusPonens(proof2, proof7)  # !p2 => !p1

        proof9 = NotToNotIntro(p2, p1).proof  # (p2 => p1) => (!p1 => !p2)
        proof10 = ModusPonens(proof6, proof9)  # !p1 => !p2

        proof11 = IIFIntro(NotProp(p1), NotProp(p2)).proof
        proof12 = ModusPonens(proof10, proof11)
        proof13 = ModusPonens(proof8, proof12)  # !p1 <=> !p2
        proof14 = Deduction(assume1, proof13).proof
        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(proof14)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class NotIIFToIIF(Theorem):
    def __init__(self, p1: Prop, p2: Prop) -> None:
        """(!p1 <=> !p2) => (p1 <=> p2)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
        """
        prop1 = IIFProp(NotProp(p1), NotProp(p2))  # !p1 <=> !p2
        assume1 = Assumption(prop1)
        proof1 = IIFElim(
            NotProp(p1), NotProp(p2)
        ).proof  # (!p1 <=> !p2) => (!p1 => !p2)
        proof2 = ModusPonens(assume1, proof1)  # !p1 => !p2
        proof3 = IIFElim(
            NotProp(p2), NotProp(p1)
        ).proof  # (!p2 <=> !p1) => (!p2 => !p1)
        proof4 = IIFExchange(
            NotProp(p1), NotProp(p2)
        ).proof  # (!p1 <=> !p2) => (!p2 <=> !p1)
        proof5 = Transitive(proof4, proof3).proof  # (!p1 <=> !p2) => (!p2 => !p1)
        proof6 = ModusPonens(assume1, proof5)  # !p2 => !p1

        proof7 = NotToNotElim(p1, p2).proof  # (!p1 => !p2) => (p2 => p1)
        proof8 = ModusPonens(proof2, proof7)  # p2 => p1

        proof9 = NotToNotElim(p2, p1).proof  # (!p2 => !p1) => (p1 => p2)
        proof10 = ModusPonens(proof6, proof9)  # p1 => p2

        proof11 = IIFIntro(p1, p2).proof
        proof12 = ModusPonens(proof10, proof11)
        proof13 = ModusPonens(proof8, proof12)  # p1 <=> p2
        proof14 = Deduction(assume1, proof13).proof  # (!p1 <=> !p2) => (p1 <=> p2)
        self.input = {"prop1": p1, "prop2": p2}
        super().__init__(proof14)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()})"


class IIFTransition(Theorem):
    def __init__(self, p1: Prop, p2: Prop, p3: Prop) -> None:
        """(p1 <=> p2) => (p2 <=> p3) => (p1 => p3)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
            p3 (Prop): _description_
        """
        prop1 = IIFProp(p1, p2)
        assume1 = Assumption(prop1)
        proof1 = ModusPonens(assume1, IIFElim(p1, p2).proof)  # p1 => p2
        proof2 = ModusPonens(assume1, IIFExchange(p1, p2).proof)  # p2 <=> p1
        proof3 = ModusPonens(proof2, IIFElim(p2, p1).proof)  # p2 => p1

        prop2 = IIFProp(p2, p3)
        assume2 = Assumption(prop2)
        proof4 = ModusPonens(assume2, IIFElim(p2, p3).proof)  # p2 => p3
        proof5 = ModusPonens(assume2, IIFExchange(p2, p3).proof)  # p3 <=> p2
        proof6 = ModusPonens(proof5, IIFElim(p3, p2).proof)  # p3 => p2

        proof7 = Transitive(proof1, proof4).proof  # p1 => p3
        proof8 = Transitive(proof6, proof3).proof  # p3 => p1

        proof9 = IIFIntro(p1, p3).proof
        proof10 = ModusPonens(proof8, ModusPonens(proof7, proof9))  # p1 <=> p3

        proof11 = Deduction(
            assume1, Deduction(assume2, proof10).proof
        ).proof  # p1 <=> p2 => p2 <=> p3 => p1 <=> p3

        self.input = {"prop1": p1, "prop2": p2, "prop3": p3}
        super().__init__(proof11)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()}, {self.input['prop3'].__str__()})"


class ForallExchange(Theorem):
    def __init__(self, p1: Prop, x1: Variable, x2: Variable) -> None:
        """(forall x1, (forall x2, p1)) => (forall x2, (forall x1, p1))

        Args:
            p1 (Prop): _description_
            x1 (Variable): _description_
            x2 (Variable): _description_
        """
        assume1 = Assumption(
            ForallProp(x1, ForallProp(x2, p1))
        )  # (forall x1, (forall x2, p1))
        prop1 = ForallProp(x2, p1)
        proof2 = ForallElimAxiom(
            prop1, x1, x1
        )  # (forall x1, (forall x2, p1)) => (forall x2, p1)
        proof3 = ModusPonens(assume1, proof2)  # forall x2, p1
        proof4 = ForallElimAxiom(p1, x2, x2)  # (forall x2, p1) => p1
        proof5 = ModusPonens(proof3, proof4)  # p1

        proof6 = Generalization(proof5, x1)  # (forall x1, p1)
        proof7 = Generalization(proof6, x2)  # (forall x2, (forall x1, p1))

        proof9 = Deduction(assume1, proof7).proof

        self.input = {"prop1": p1, "var1": x2, "var2": x2}
        super().__init__(proof9)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['var1'].__str__()}, {self.input['var2'].__str__()})"


class ExistIntro(Theorem):
    def __init__(self, prop: Prop, x: Variable, y: Variable) -> None:
        """prop[x->y] => (exists x, prop)

        Args:
            prop (Prop): _description_
            x (Variable): _description_
            y (Variable): _description_
        """
        proof1 = ForallElimAxiom(
            NotProp(prop), x, y
        )  # (forall x, !prop) => !prop[x -> y]

        prop1: ImplyProp = proof1.prop  # type: ignore
        proof2 = NotToNotIntro(prop1.left_child, prop1.right_child).proof
        proof3 = ModusPonens(proof1, proof2)  # !!prop[x -> y] => !(forall x, !prop)
        prop5: NotProp = prop1.right_child  # type: ignore
        proof4 = DoubleNotIntro(prop5.child).proof  # prop[x -> y] => !!prop[x -> y]
        proof5 = Transitive(proof4, proof3).proof  # prop[x -> y] => !(forall x, !prop)

        prop4 = ExistProp(x, prop)
        proof6 = FromEvalAxiom(prop4)

        proof7 = Transitive(proof5, proof6).proof

        self.input = {"prop1": prop, "var1": x, "var2": y}
        super().__init__(proof7)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['var1'].__str__()}, {self.input['var2'].__str__()})"


class ForallXYToForallX(Theorem):
    def __init__(self, prop: Prop, x: Variable, y: Variable) -> None:
        """(forall x, (forall y, prop)) => (forall x, prop[y->x])

        Args:
            prop (Prop): _description_
            x (Variable): _description_
            y (Variable): _description_
        """
        assume1 = Assumption(ForallProp(x, ForallProp(y, prop)))
        proof1 = ForallElimAxiom(ForallProp(y, prop), x, x)
        proof2 = ModusPonens(assume1, proof1)  # forall y, prop
        proof3 = ForallElimAxiom(prop, y, x)  # (forall y, prop) => prop[y->x]
        proof4 = ModusPonens(proof2, proof3)  # prop[y->x]
        proof5 = Generalization(proof4, x)  # forall x, prop[y->x]
        proof6 = Deduction(assume1, proof5).proof

        self.input = {"prop1": prop, "var1": x, "var2": y}
        super().__init__(proof6)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['var1'].__str__()}, {self.input['var2'].__str__()})"


class ForallImplyToImplyForall(Theorem):
    def __init__(self, prop1: Prop, prop2: Prop, x: Variable) -> None:
        """(forall x, prop1 => prop2) => (forall x, prop1) => (forall x, prop2)

        Args:
            prop1 (Prop): _description_
            prop2 (Prop): _description_
            x (Variable): _description_
        """
        assume1 = Assumption(
            ForallProp(x, ImplyProp(prop1, prop2))
        )  # (forall x, prop1 => prop2)
        proof1 = ForallElimAxiom(ImplyProp(prop1, prop2), x, x)
        proof2 = ModusPonens(assume1, proof1)  # prop1 => prop2
        proof3 = ForallElimAxiom(prop1, x, x)  # (forall x, prop1) => prop1
        proof4 = Transitive(proof3, proof2).proof  # (forall x, prop1) => prop2
        proof5 = Generalization(proof4, x)  # (forall x, (forall x, prop1) => prop2)
        proof6 = ForallImplyExchangeAxiom(
            ForallProp(x, prop1), prop2, x
        )  # (forall x, (forall x, prop1) => prop2) => (forall x, prop1) => (forall x, prop2)
        proof7 = ModusPonens(proof5, proof6)  # (forall x, prop1) => (forall x, prop2)
        proof8 = Deduction(assume1, proof7).proof

        self.input = {"prop1": prop1, "prop2": prop2, "var1": x}
        super().__init__(proof8)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()}, {self.input['var1'].__str__()})"


class ForallImplyToImplyExist(Theorem):
    def __init__(self, prop1: Prop, prop2: Prop, x: Variable) -> None:
        """(forall x, prop1 => prop2) => (exists x, prop1) => (exists x, prop2)

        Args:
            prop1 (Prop): _description_
            prop2 (Prop): _description_
            x (Variable): _description_
        """
        assume1 = Assumption(
            ForallProp(x, ImplyProp(prop1, prop2))
        )  # (forall x, prop1 => prop2)
        proof1 = ForallElimAxiom(ImplyProp(prop1, prop2), x, x)
        proof2 = ModusPonens(assume1, proof1)  # prop1 => prop2
        proof3 = NotToNotIntro(
            prop1, prop2
        ).proof  # (prop1 => prop2) => (!prop2 => !prop1)
        proof4 = ModusPonens(proof2, proof3)  # !prop2 => !prop1

        proof5 = ForallElimAxiom(NotProp(prop2), x, x)  # (forall x, !prop2) => !prop2
        proof6 = Transitive(proof5, proof4).proof  # (forall x, !prop2) => !prop1
        proof7 = Generalization(proof6, x)  # (forall x, (forall x, !prop2) => !prop1)
        proof8 = ForallImplyExchangeAxiom(
            ForallProp(x, NotProp(prop2)), NotProp(prop1), x
        )  # (forall x, (forall x, !prop2) => !prop1) => (forall x, !prop2) => (forall x, !prop1)
        proof9 = ModusPonens(proof7, proof8)  # (forall x, !prop2) => (forall x, !prop1)

        proof10 = NotToNotIntro(
            ForallProp(x, NotProp(prop2)), ForallProp(x, NotProp(prop1))
        ).proof
        proof11 = ModusPonens(
            proof9, proof10
        )  # !(forall x, !prop1) => !(forall x, !prop2)

        prop3 = ExistProp(x, prop1)
        prop4 = ExistProp(x, prop2)

        proof12 = ToEvalAxiom(prop3)
        proof13 = FromEvalAxiom(prop4)

        proof14 = Transitive(
            proof12, proof11
        ).proof  # (exists x, prop1) => !(forall x, !prop2)
        prop5: ImplyProp = proof14.prop  # type: ignore
        proof14_1 = ToEvalAxiom(prop5.right_child)
        proof14_2 = Transitive(proof14, proof14_1).proof
        proof15 = Transitive(
            proof14_2, proof13
        ).proof  # (exists x, prop1) => (exists x, prop2)

        proof16 = Deduction(assume1, proof15).proof
        self.input = {"prop1": prop1, "prop2": prop2, "var1": x}
        super().__init__(proof16)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()}, {self.input['var1'].__str__()})"


class ForallAndToAndForall(Theorem):
    def __init__(self, prop1: Prop, prop2: Prop, x: Variable) -> None:
        """(forall x, prop1 /\\ prop2) => (forall x, prop1) /\\ (forall x, prop2)

        Args:
            prop1 (Prop): _description_
            prop2 (Prop): _description_
            x (Variable): _description_
        """
        prop3 = AndProp(prop1, prop2)
        assume1 = Assumption(ForallProp(x, AndProp(prop1, prop2)))
        proof1 = ForallElimAxiom(prop3, x, x)
        proof2 = ModusPonens(assume1, proof1)  # prop1 /\\ prop2
        proof3 = AndElim(prop1, prop2).proof  # prop1 /\\ prop2  => prop2
        proof4 = ModusPonens(proof2, proof3)  # prop2
        proof5 = Generalization(proof4, x)  # (forall x, prop2)

        proof6 = AndExchange(prop1, prop2).proof
        proof7 = ModusPonens(proof2, proof6)  # prop2 /\\ prop1
        proof8 = AndElim(prop2, prop1).proof  # prop2 /\\ prop1 => prop1
        proof9 = ModusPonens(proof7, proof8)  # prop1
        proof10 = Generalization(proof9, x)  # (forall x, prop1)

        proof11 = AndIntro(ForallProp(x, prop1), ForallProp(x, prop2)).proof
        proof12 = ModusPonens(proof10, proof11)
        proof13 = ModusPonens(
            proof5, proof12
        )  # (forall x, prop1) /\\ (forall x, prop2)

        proof14 = Deduction(assume1, proof13).proof

        self.input = {"prop1": prop1, "prop2": prop2, "var1": x}
        super().__init__(proof14)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()}, {self.input['var1'].__str__()})"


class NotForallToExistNot(Theorem):
    def __init__(self, prop1: Prop, x: Variable) -> None:
        """!(forall x, prop1) => (exists x, !prop1)

        Args:
            proof (Proof): _description_
        """
        prop2 = NotProp(NotProp(prop1))
        prop3 = ForallProp(x, NotProp(NotProp(prop1)))
        assume1 = Assumption(prop3)
        proof1 = ForallElimAxiom(prop2, x, x)  # (forall x, !!prop1) => !!prop1
        proof2 = ModusPonens(assume1, proof1)  # !!prop1
        proof3 = DoubleNotElim(prop1).proof  # !!prop1 => prop1
        proof4 = ModusPonens(proof2, proof3)  # prop1
        proof5 = Generalization(proof4, x)  # (forall x, prop1)
        proof6 = Deduction(
            assume1, proof5
        ).proof  # (forall x, !!prop1) => (forall x, prop1)
        proof7 = NotToNotIntro(prop3, ForallProp(x, prop1)).proof
        proof8 = ModusPonens(
            proof6, proof7
        )  # !(forall x, prop1) => !(forall x, !!prop1)

        prop3 = ExistProp(x, NotProp(prop1))
        proof9 = FromEvalAxiom(prop3)
        proof10 = Transitive(
            proof8, proof9
        ).proof  # !(forall x, prop1) => (exists x, !prop1)

        self.input = {"prop1": prop1, "var1": x}
        super().__init__(proof10)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['var1'].__str__()})"


class OrForallToForallOr(Theorem):
    def __init__(self, prop1: Prop, prop2: Prop, x: Variable) -> None:
        """[(forall x, prop1) \\/ (forall x, prop2)] => (forall x, prop1 \\/ prop2)

        Args:
            prop1 (Prop): _description_
            prop2 (Prop): _description_
            x (Variable): _description_
        """
        prop3 = OrProp(ForallProp(x, prop1), ForallProp(x, prop2))
        assume1 = Assumption(prop3)
        proof1 = ToEvalAxiom(prop3)
        proof2 = ModusPonens(assume1, proof1)  # !(forall x, prop1) => (forall x, prop2)
        proof3 = ForallElimAxiom(prop2, x, x)  # (forall x, prop2) => prop2
        proof4 = Transitive(proof2, proof3).proof  # !(forall x, prop1) => prop2

        proof5 = NotImplyExchange(ForallProp(x, prop1), prop2).proof
        proof6 = ModusPonens(proof4, proof5)  # !prop2 => (forall x, prop1)
        proof7 = ForallElimAxiom(prop1, x, x)  # (forall x, prop1) => prop1
        proof8 = Transitive(proof6, proof7).proof  # !prop2 => prop1

        proof9 = NotImplyExchange(
            prop2, prop1
        ).proof  # (!prop2 => prop1) => (!prop1 => prop2)
        proof10 = ModusPonens(proof8, proof9)  # !prop1 => prop2

        prop2 = OrProp(prop1, prop2)
        proof11 = FromEvalAxiom(prop2)  # !prop1 => prop2 => (prop1 \/ prop2)
        proof12 = ModusPonens(proof10, proof11)  # prop1 \/ prop2

        proof13 = Generalization(proof12, x)  # (forall x, prop1 \/ prop2)
        proof14 = Deduction(assume1, proof13).proof

        self.input = {"prop1": prop1, "prop2": prop2, "var1": x}
        super().__init__(proof14)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()}, {self.input['var1'].__str__()})"


class ForallOrToOrForallExist(Theorem):
    def __init__(self, p1: Prop, p2: Prop, x: Variable) -> None:
        """(forall x, p1 \\/ p2) => (forall x, p1) \\/ (exists x, p2)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
            x (Variable): _description_
        """
        prop1 = OrProp(p1, p2)
        assume1 = Assumption(ForallProp(x, prop1))
        proof1 = ForallElimAxiom(prop1, x, x)
        proof2 = ModusPonens(assume1, proof1)  # p1 \\/ p2
        proof3 = OrExchange(p1, p2).proof  # p1 \\/ p2 => p2 \\/ p1
        proof4 = ModusPonens(proof2, proof3)  # p2 \\/ p1
        prop2 = OrProp(p2, p1)
        proof5 = ToEvalAxiom(prop2)
        proof6 = ModusPonens(proof4, proof5)  # !p2 => p1
        proof7 = ForallElimAxiom(NotProp(p2), x, x)  # (forall x, !p2) => !p2
        proof8 = Transitive(proof7, proof6).proof  # (forall x, !p2) => p1
        proof9 = Generalization(proof8, x)  # (forall x, (forall x, !p2) => p1)

        proof10 = ForallImplyExchangeAxiom(
            ForallProp(x, NotProp(p2)), p1, x
        )  # (forall x, (forall x, !p2) => p1) => (forall x, !p2) => (forall x, p1)
        proof11 = ModusPonens(proof9, proof10)  # (forall x, !p2) => (forall x, p1)

        proof12 = NotToNotIntro(ForallProp(x, NotProp(p2)), ForallProp(x, p1)).proof
        proof13 = ModusPonens(proof11, proof12)  # !(forall x, p1) => !(forall x, !p2)

        prop3 = OrProp(ForallProp(x, p1), ExistProp(x, p2))
        proof14 = FromEvalAxiom(prop3)

        proof15 = ModusPonens(proof13, proof14)  # (forall x, p1) \\/ (exists x, p2)

        proof16 = Deduction(assume1, proof15).proof

        self.input = {"prop1": p1, "prop2": p2, "var1": x}
        super().__init__(proof16)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()}, {self.input['var1'].__str__()})"


class ForallNotToForallNotIntro(Theorem):
    def __init__(self, p1: Prop, p2: Prop, x: Variable) -> None:
        """(forall x, p1 => p2) => (forall x, !p2) => (forall x, !p1)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
            x (Variable): _description_
        """
        assume1 = Assumption(ForallProp(x, ImplyProp(p1, p2)))
        proof1 = ForallElimAxiom(ImplyProp(p1, p2), x, x)
        proof2 = ModusPonens(assume1, proof1)  # p1 => p2
        proof3 = NotToNotIntro(p1, p2).proof
        proof4 = ModusPonens(proof2, proof3)  # !p2 => !p1
        proof5 = ForallElimAxiom(NotProp(p2), x, x)
        proof6 = Transitive(proof5, proof4).proof  # (forall x, !p2) => !p1
        proof7 = Generalization(proof6, x)  # (forall x, (forall x, !p2) => !p1)
        proof8 = ForallImplyExchangeAxiom(ForallProp(x, NotProp(p2)), NotProp(p1), x)
        proof9 = ModusPonens(proof7, proof8)  # (forall x, !p2) => (forall x, !p1)
        proof10 = Deduction(assume1, proof9).proof

        self.input = {"prop1": p1, "prop2": p2, "var1": x}
        super().__init__(proof10)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()}, {self.input['var1'].__str__()})"


class ForallImplyExist(Theorem):
    def __init__(self, p1: Prop, x: Variable, y: Variable):
        """(forall x, p1[y->x] => (exists y, p1))

        Args:
            p1 (Prop): _description_
            x (Variable): _description_
            y (Variable): _description_
        """
        proof1 = ForallElimAxiom(NotProp(p1), y, x)  # (forall y, !p1) => !p1[y -> x]
        prop1: ImplyProp = proof1.prop  # type: ignore
        prop2: NotProp = prop1.right_child  # type:ignore
        proof2 = ImplyNotExchange(prop1.left_child, prop2.child).proof
        proof3 = ModusPonens(proof1, proof2)  # p1[y -> x] => !(forall y, !p1)
        prop3 = ExistProp(y, p1)
        proof4 = FromEvalAxiom(prop3)
        proof5 = Transitive(proof3, proof4).proof  # p1[y -> x] => (exists y, p1)

        proof6 = Generalization(proof5, x)
        self.input = {"prop1": p1, "var1": x, "var2": y}
        super().__init__(proof6)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['var1'].__str__()}, {self.input['var2'].__str__()})"


class NotExistToForallNot(Theorem):
    def __init__(self, p1: Prop, x: Variable) -> None:
        """!(exists x, p1) => (forall x, !p1)

        Args:
            proof (Proof): _description_
        """
        prop1 = ExistProp(x, p1)
        proof1 = FromEvalAxiom(prop1)  # !(forall x, !p1) => (exists x, p1)
        proof2 = NotImplyExchange(ForallProp(x, NotProp(p1)), ExistProp(x, p1)).proof
        proof3 = ModusPonens(proof1, proof2)  # !(exists x, p1) => (forall x, !p1)

        self.input = {"prop1": p1, "var1": x}
        super().__init__(proof3)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['var1'].__str__()}"


class ExistToExistExist(Theorem):
    def __init__(self, p1: Prop, x: Variable, y: Variable) -> None:
        """(exists x, p1[y -> x]) => (exists x, (exists y, p1))

        Args:
            p1 (Prop): _description_
            x (Variable): _description_
            y (Variable): _description_
        """
        proof1 = ForallElimAxiom(NotProp(p1), y, x)  # (forall y, !p1) => !p1[y -> x]
        prop1: ImplyProp = proof1.prop  # type: ignore
        prop2: NotProp = prop1.right_child  # type: ignore
        proof2 = ImplyNotExchange(prop1.left_child, prop2.child).proof
        proof3 = ModusPonens(proof1, proof2)  # p1[y -> x] => !(forall y, !p1)
        prop3 = ExistProp(y, p1)
        proof4 = FromEvalAxiom(prop3)  # !(forall y, !p1) => (exists y, p1)
        proof5 = Transitive(proof3, proof4).proof  # p1[y -> x] => (exists y, p1)
        proof6 = Generalization(proof5, x)  # (forall x, p1[y -> x] => (exists y, p1))
        prop4: ImplyProp = proof5.prop  # type: ignore
        proof7 = ForallImplyToImplyExist(prop4.left_child, prop4.right_child, x).proof
        proof8 = ModusPonens(
            proof6, proof7
        )  # (exists x, p1[y -> x]) => (exists x, (exists y, p1))

        self.input = {"prop1": p1, "var1": x, "var2": y}
        super().__init__(proof8)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['var1'].__str__()}, {self.input['var2'].__str__()})"


class NotFreeVarForallIntro(Theorem):
    def __init__(self, p1: Prop, x: Variable) -> None:
        """p1 => (forall x, p1)

        Args:
            p1 (Prop): _description_
            x (Variable): x should not be free in p1
        """
        if p1.isfree(x):
            raise ValueError("ImplyForallIIFForall(): x should be free in p1")
        proof1 = Reflexive(p1).proof  # p1 => p1
        proof2 = Generalization(proof1, x)  # (forall x, p1 => p1)
        proof3 = ForallImplyExchangeAxiom(p1, p1, x)
        proof4 = ModusPonens(proof2, proof3)  # p1 => (forall x, p1)

        self.input = {"prop1": p1, "var1": x}
        super().__init__(proof4)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['var1'].__str__()})"


class NotFreeVarExistElim(Theorem):
    def __init__(self, p1: Prop, x: Variable) -> None:
        """(exist x, p1) => p1

        Args:
            p1 (Prop): _description_
            x (Variable): x should not be free in p1
        """
        proof1 = NotFreeVarForallIntro(NotProp(p1), x).proof
        proof2 = NotImplyExchange(p1, ForallProp(x, NotProp(p1))).proof
        proof3 = ModusPonens(proof1, proof2)  # !(forall x, !p1) => p1
        proof4 = ToEvalAxiom(ExistProp(x, p1))
        proof5 = Transitive(proof4, proof3).proof  # (exist x, p1) => p1

        self.input = {"prop1": p1, "var1": x}
        super().__init__(proof5)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['var1'].__str__()})"


class NotFreeVarImplyForallIIFForall(Theorem):
    def __init__(self, p1: Prop, p2: Prop, x: Variable) -> None:
        """(p1 => (forall x, p2)) <=> (forall x, p1 => p2)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
            x (Variable): x is not free in p1
        """
        if p1.isfree(x):
            raise ValueError("ImplyForallIIFForall(): x should be free in p1")

        proof1 = ForallImplyExchangeAxiom(
            p1, p2, x
        )  # (forall x, p1 => p2) => (p1 => (forall x, p2))

        assume1 = Assumption(ImplyProp(p1, ForallProp(x, p2)))
        proof3 = ForallElimAxiom(p2, x, x)  # (forall x, p2) => p2
        proof4 = Transitive(assume1, proof3).proof  # p1 => p2
        proof5 = Generalization(proof4, x)
        proof6 = Deduction(assume1, proof5).proof

        proof7 = IIFIntro(
            ImplyProp(p1, ForallProp(x, p2)), ForallProp(x, ImplyProp(p1, p2))
        ).proof
        proof8 = ModusPonens(proof6, proof7)
        proof9 = ModusPonens(proof1, proof8)

        self.input = {"prop1": p1, "prop2": p2, "var1": x}
        super().__init__(proof9)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()}, {self.input['var1'].__str__()})"


class NotFreeVarImplyExistIIFForall(Theorem):
    def __init__(self, p1: Prop, p2: Prop, x: Variable) -> None:
        """((exists x, p2) => p1) => (forall x, (p2 => p1))

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
            x (Variable): x should not be free in p1
        """
        prop1 = ForallProp(x, ImplyProp(p2, p1))
        assume1 = Assumption(prop1)  # (forall x, p2 => p1)
        proof1 = ForallImplyToImplyExist(p2, p1, x).proof
        proof2 = ModusPonens(assume1, proof1)  # (exists x, p2) => (exists x, p1)
        proof3 = NotFreeVarExistElim(p1, x).proof  # (exists x, p1) => p1
        proof4 = Transitive(proof2, proof3).proof  # (exists x1, p2) => p1
        proof5 = Deduction(
            assume1, proof4
        ).proof  # (forall x, p2 => p1) => ((exists x1, p2) => p1)

        prop2 = ImplyProp(ExistProp(x, p2), p1)
        assume2 = Assumption(prop2)  # (exists x, p2) => p1
        proof6 = FromEvalAxiom(ExistProp(x, p2))
        proof7 = Transitive(proof6, assume2).proof  # (!(forall x, !p2) => p1)
        proof8 = NotImplyExchange(ForallProp(x, NotProp(p2)), p1).proof
        proof9 = ModusPonens(proof7, proof8)  # !p1 => (forall x, !p2)
        proof10 = ForallElimAxiom(NotProp(p2), x, x)
        proof11 = Transitive(proof9, proof10).proof  # !p1 => !p2
        proof12 = NotToNotElim(p1, p2).proof
        proof13 = ModusPonens(proof11, proof12)  # p2 => p1
        proof14 = Generalization(proof13, x)  # (forall x, p2 => p1)
        proof15 = Deduction(
            assume2, proof14
        ).proof  # ((exists x, p2) => p1) => (forall x, p2 => p1)

        proof16 = IIFIntro(prop2, prop1).proof
        proof17 = ModusPonens(proof15, proof16)
        proof18 = ModusPonens(proof5, proof17)

        self.input = {"prop1": p1, "prop2": p2, "var1": x}
        super().__init__(proof18)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()}, {self.input['var1'].__str__()})"


class ForallIIFExchange(Theorem):
    def __init__(self, p1: Prop, p2: Prop, x: Variable) -> None:
        """(forall x, p1 <=> p2) => (forall x, p1) <=> (forall x, p2)

        Args:
            p1 (Prop): _description_
            p2 (Prop): _description_
            x (Variable): _description_
        """
        assume1 = Assumption(ForallProp(x, IIFProp(p1, p2)))
        assume2 = Assumption(ForallProp(x, p1))
        assume3 = Assumption(ForallProp(x, p2))

        proof1 = ForallElimAxiom(IIFProp(p1, p2), x, x)
        proof2 = ModusPonens(assume1, proof1)  # p1 <=> p2
        proof21 = IIFElim(p1, p2).proof
        proof22 = ModusPonens(proof2, proof21)  # p1 => p2
        proof3 = ForallElimAxiom(p1, x, x)
        proof4 = ModusPonens(assume2, proof3)  # p1
        proof5 = ModusPonens(proof4, proof22)  # p2
        proof6 = Generalization(proof5, x)  # (forall x, p2)
        proof7 = Deduction(assume2, proof6).proof  # (forall x, p1) => (forall x, p2)

        proof9 = IIFExchange(p1, p2).proof
        proof10 = ModusPonens(proof2, proof9)  # p2 <=> p1
        proof11 = IIFElim(p2, p1).proof
        proof12 = ModusPonens(proof10, proof11)  # p2 => p1
        proof13 = ForallElimAxiom(p2, x, x)
        proof14 = ModusPonens(assume3, proof13)  # p2
        proof15 = ModusPonens(proof14, proof12)  # p1
        proof16 = Generalization(proof15, x)  # (forall x, p1)
        proof17 = Deduction(assume3, proof16).proof  # (forall x, p2) => (forall x, p1)

        proof18 = IIFIntro(ForallProp(x, p1), ForallProp(x, p2)).proof
        proof19 = ModusPonens(proof7, proof18)
        proof20 = ModusPonens(proof17, proof19)  # (forall x, p1) <=> (forall x, p2)

        proof21 = Deduction(assume1, proof20).proof

        self.input = {"prop1": p1, "prop2": p2, "var1": x}
        super().__init__(proof21)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['prop2'].__str__()}, {self.input['var1'].__str__()})"
