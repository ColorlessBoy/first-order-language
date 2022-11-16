from __future__ import annotations


class Variable:
    def __init__(self, content: str) -> None:
        self.content = content

    def __eq__(self, other: Variable) -> bool:
        return self.content == other.content

    def __hash__(self) -> int:
        return self.content.__hash__()

    def __str__(self) -> str:
        return self.content.__str__()
