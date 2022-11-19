from __future__ import annotations


class Variable:
    def __init__(self, content: str) -> None:
        self.content = content

    def alphaEq(
        self,
        other: Variable,
        self_var_to_int: dict[Variable, int],
        other_var_to_int: dict[Variable, int],
    ):
        if self not in self_var_to_int:
            value = len(self_var_to_int)
            self_var_to_int[self] = value
        if other not in other_var_to_int:
            value = len(other_var_to_int)
            other_var_to_int[other] = value
        return self_var_to_int[self] == other_var_to_int[other]

    def __eq__(self, __o: Variable) -> bool:
        return self.content == __o.content

    def __hash__(self) -> int:
        return self.content.__hash__()

    def __str__(self) -> str:
        return self.content.__str__()
