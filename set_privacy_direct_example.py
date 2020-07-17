#!/usr/bin/env python3
from z3 import And, Or, IntSort

from set_privacy_direct import check_privacy, SelectProjectQuery


def main() -> None:
    schema = {"a": IntSort(), "b": IntSort()}

    constraints = [
        SelectProjectQuery(["a"], lambda a, b: a * b == 0),
        SelectProjectQuery(["b"], lambda a, b: a == 42),
    ]
    query = SelectProjectQuery(["b"], lambda a, b: Or(And(Or(a == 0, b == 0), a > 0),
                                                      And(a == b * (b + 1), b == 6)))
    print(check_privacy(schema, constraints, query))


if __name__ == "__main__":
    main()
