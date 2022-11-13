from __future__ import annotations


class Variable:
    def __init__(self, name: str) -> None:
        self.name = name

    def __eq__(self, other: Variable) -> bool:
        return self.name == other.name

    def __hash__(self) -> int:
        return self.name.__hash__()

    def __str__(self) -> str:
        return self.name.__str__()
