from __future__ import annotations


class Variable:
    def __init__(self, content: str) -> None:
        self.content = content

    def __eq__(self, __o: Variable) -> bool:
        return self.content == __o.content

    def __hash__(self) -> int:
        return self.content.__hash__()

    def __str__(self) -> str:
        return self.content.__str__()
