#!/usr/bin/env python3
from typing import Any, Dict, Sequence, Tuple
from dataclasses import dataclass
from itertools import product

import z3


Tup = Tuple[Tuple[str, Any]]


def tup_to_str(tup):
    return ",".join(str(p[1]) for p in tup)


def project_tup(tup, kept_columns):
    d = dict(tup)
    new_l = [(c, d[c]) for c in kept_columns]
    return tuple(new_l)


@dataclass
class Table:
    universe: Sequence[Any]
    columns: Sequence[str]
    counts: Dict[Tup, Any]
    assumptions: Any = True

    @staticmethod
    def make_all_tuples(universe, columns):
        return (tuple(zip(columns, c)) for c in product(universe, repeat=len(columns)))

    @staticmethod
    def create_empty(universe, columns):
        return Table(universe, columns, {tup: 0 for tup in Table.make_all_tuples(universe, columns)})

    @staticmethod
    def create_symbolic(name, universe, columns):
        counts = {}
        assumptions = True
        for tup in Table.make_all_tuples(universe, columns):
            var = z3.Int(f"{name}.{tup_to_str(tup)}")
            counts[tup] = var
            assumptions = z3.And(assumptions, var >= 0)
        return Table(universe, columns, counts, assumptions)

    @property
    def vars(self):
        return list(self.counts.values())

    # theta takes keyword arguments.
    def filter(self, theta) -> "Table":
        new_table = Table(self.universe, self.columns, {})
        for tup, count in self.counts.items():
            new_table.counts[tup] = z3.If(theta(**dict(tup)), count, 0)
            # if theta(**dict(tup)):
            #     new_table.counts[tup] = count
            # else:
            #     new_table.counts[tup] = 0
        return new_table

    def project(self, kept_columns: Sequence[str]):
        new_table = Table.create_empty(self.universe, kept_columns)
        for tup, count in self.counts.items():
            new_tup = project_tup(tup, kept_columns)
            new_table.counts[new_tup] += count
        return new_table

    def __eq__(self, other: "Table"):
        assert self.universe == other.universe
        assert self.columns == other.columns
        formula = True
        for tup in self.counts:
            formula = z3.And(formula, self.counts[tup] == other.counts[tup])
        return formula

    def is_disjoint_from(self, other: "Table"):
        assert self.universe == other.universe
        assert self.columns == other.columns
        formula = True
        for tup in self.counts:
            formula = z3.And(formula, z3.Or(self.counts[tup] == 0, other.counts[tup] == 0))
        return formula

    def is_subset_of(self, other: "Table"):
        assert self.universe == other.universe
        assert self.columns == other.columns
        formulas = []
        for tup in self.counts:
            formulas.append(self.counts[tup] <= other.counts[tup])
        return z3.And(formulas)

    def is_proper_subset_of(self, other: "Table"):
        return z3.And(self.is_subset_of(other), z3.Not(self == other))

    def has_no_duplicates(self):
        formula = True
        for count in self.counts.values():
            formula = z3.And(formula, count <= 1)
        return formula

    def size(self):
        formula = 0
        for count in self.counts.values():
            formula += count
        return formula

    def print_instance(self, model):
        print("\t".join(self.columns))
        print("\t".join("---" for _ in self.columns))
        for tup in sorted(self.counts.keys()):
            instance_count = model.evaluate(self.counts[tup])
            line = "\t".join(str(value) for _, value in tup)
            for _ in range(instance_count.as_long()):
                print(line)


def congruent(r1, r2, q):
    return q(r1) == q(r2)


def main():
    universe = [0, 1, 2]
    columns = ["a", "b", "c"]
    r1 = Table.create_symbolic("r1", universe, columns)
    r2 = Table.create_symbolic("r2", universe, columns)

    sol = z3.Solver()
    sol.add(r1.assumptions)
    sol.add(r2.assumptions)

    sol.add(congruent(r1, r2, lambda r: r.project(["a", "b"])))
    sol.add(congruent(r1, r2, lambda r: r.project(["b", "c"])))
    sol.add(congruent(r1, r2, lambda r: r.project(["a", "c"])))
    sol.add(z3.Not(congruent(r1, r2,
                             lambda r: r.filter(
                                 lambda a, b, c: a == b or b == c
                             ).project([]))))
    sol.add(r1.size() <= 4)

    res = sol.check()
    if res == z3.sat:
        model = sol.model()
        r1.print_instance(model)
        print()
        r2.print_instance(model)
    else:
        print(res)


if __name__ == "__main__":
    main()

