from __future__ import annotations

from extprop import AndProp, ExistProp, FromEvalAxiom, IIFProp, OrProp, ToEvalAxiom
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
            "ToEvalAxiom",
            "FromEvalAxiom",
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


class ExistIntro(Theorem):
    def __init__(self, prop: Prop, x: Variable, y: Variable) -> None:
        """prop[x=>y] => (exist x, prop)

        Args:
            prop (Prop): _description_
            x (Variable): _description_
            y (Variable): _description_
        """
        proof1 = Axiom4(NotProp(prop), x, y)  # (forall x, !prop) => !prop[x => y]
        prop1: ImplyProp = proof1.prop  # type: ignore
        proof2 = NotToNotIntro(prop1.left_child, prop1.right_child).proof
        proof3 = ModusPonens(proof1, proof2)  # !!prop[x => y] => !(forall x, !prop)
        prop5: NotProp = prop1.right_child  # type: ignore
        proof4 = DoubleNotIntro(prop5.child).proof  # prop[x => y] => !!prop[x => y]
        proof5 = Transitive(proof4, proof3).proof  # prop[x => y] => !(forall x, !prop)

        prop4 = ExistProp(x, prop)
        proof6 = FromEvalAxiom(prop4)

        proof7 = Transitive(proof5, proof6).proof

        self.input = {"prop1": prop, "variable1": x, "variable2": y}
        super().__init__(proof7)

    def __str__(self) -> str:
        return f"{self.getname()}({self.input['prop1'].__str__()}, {self.input['variable1'].__str__()}, {self.input['variable2'].__str__()})"


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
        prop1 = AndProp(p1, p2)  # p1 /\\ p2
        proof7 = FromEvalAxiom(prop1)  # !(p1 => !p2) => p1 /\\ p2
        proof8 = Transitive(proof6, proof7).proof  # p2 => p1 /\\ p2
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
