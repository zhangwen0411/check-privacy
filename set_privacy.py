#!/usr/bin/env python3
from typing import Any, Sequence
from dataclasses import dataclass

import z3


@dataclass
class Table:
    columns: Sequence[str]
    sort: Any
    does_contain: Any

    @staticmethod
    def create_symbolic(name, sort, columns):
        assert len(columns) == len(set(columns))
        sig = [sort] * len(columns) + [z3.BoolSort()]
        relation = z3.Function(name, *sig)
        return Table(columns, sort, lambda *tup: relation(*tup))

    def filter(self, theta) -> "Table":
        def does_contain(*tup):
            assert len(tup) == len(self.columns)
            return z3.And(self.does_contain(*tup), theta(*tup))

        return Table(self.columns, self.sort, does_contain)

    def project(self, kept_columns: Sequence[str]):
        kcs = set(kept_columns)
        assert len(kept_columns) == len(kcs)
        assert set(self.columns).issuperset(kcs)

        def does_contain(*tup):
            assert len(tup) == len(kept_columns)
            col_map = dict(zip(kept_columns, tup))
            variables = []
            existentials = []
            for c in self.columns:
                if c in col_map:
                    variables.append(col_map[c])
                else:
                    var = z3.Const(c, self.sort)
                    existentials.append(var)
                    variables.append(var)
            return z3.Exists(existentials, self.does_contain(*variables))

        return Table(kept_columns, self.sort, does_contain)

    def __eq__(self, other: "Table"):
        assert self.sort == other.sort
        assert self.columns == other.columns
        variables = [z3.Const(c, self.sort) for c in self.columns]
        body = self.does_contain(*variables) == other.does_contain(*variables)
        if variables:
            return z3.ForAll(variables, body)
        else:
            return body

    def disjoint_from(self, other: "Table"):
        assert self.sort == other.sort
        assert self.columns == other.columns
        variables = [z3.Const(c, self.sort) for c in self.columns]
        body = z3.Not(z3.And(self.does_contain(*variables), other.does_contain(*variables)))
        if variables:
            return z3.ForAll(variables, body)
        else:
            return body


def congruent(r1, r2, q):
    return q(r1) == q(r2)


def main():
    sort = z3.DeclareSort("S")  # Unbounded number of distinct values...
    # sort, _ = z3.EnumSort("S", ["x", "y"]) # Or bounded number of distinct values (here we have two).
    columns = ["a", "b", "c"]  # All columns take values from the same sort, for now.
    r1 = Table.create_symbolic("r1", sort, columns)
    r2 = Table.create_symbolic("r2", sort, columns)

    # Dear solver,
    sol = z3.Solver()
    # r1 and r2 are congruent under \pi_{a, b},
    sol.add(congruent(r1, r2, lambda r: r.project(["a", "b"])))
    # and are congruent under \pi_{b, c},
    sol.add(congruent(r1, r2, lambda r: r.project(["b", "c"])))
    # but are NOT congruent under \pi_{b} \sigma_{a == b == c};
    sol.add(z3.Not(congruent(r1, r2, lambda r: r.filter(lambda a, b, c: z3.And(a == b, b == c)).project(["b"]))))

    # is this possible?
    res = sol.check()
    if res == z3.sat:
        print(sol.model())
    else:
        print(res)


if __name__ == "__main__":
    main()
