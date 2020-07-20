"""Implements privacy checking under set semantics according to Claim 7.8."""
from dataclasses import dataclass
import sys
from typing import Callable, Dict, Sequence, Iterable, List

from IPython.display import display
from z3 import And, BoolRef, Const, ExprRef, ForAll, Implies, Not, Or, sat, simplify, Solver, SortRef, unsat

Schema = Dict[str, SortRef]  # Maps column name to sort.


class DBTuple(Dict[str, ExprRef]):
    """A symbolic database tuple."""
    def __getitem__(self, item):
        """Overloaded to support restriction to a set of columns."""
        if isinstance(item, str):
            return super(DBTuple, self).__getitem__(item)

        # Assume that item is an iterable of column names.
        assert isinstance(item, (list, tuple))
        return DBTuple({c: self[c] for c in item})

    def __eq__(self, other: "DBTuple") -> bool:
        """Expression for tuple equality."""
        # Can only check equality between tuples with the same set of columns.
        assert set(self.keys()) == set(other.keys())
        return And([self[c] == other[c] for c in self])


@dataclass
class SelectProjectQuery:
    U: Sequence[str]
    # Takes values as keyword arguments, returns a Z3 bool expression.
    theta: Callable[..., BoolRef] = lambda **kwargs: True


def for_all_tuples(name: str, schema: Schema, f: Callable[[DBTuple], BoolRef]) -> BoolRef:
    if not schema:  # No columns.
        return f(DBTuple())

    tup = DBTuple({column: Const(f"{name}_{column}", sort) for column, sort in schema.items()})
    bound_vars = list(tup.values())
    return ForAll(bound_vars, f(tup))


def check_privacy(schema: Schema,
                  constraints: Iterable[SelectProjectQuery],
                  query: SelectProjectQuery,
                  *, verbose=False
                  ) -> bool:
    theta = query.theta
    U = query.U

    def inner(t: DBTuple) -> BoolRef:
        clauses: List[BoolRef] = []
        for s_i in constraints:
            theta_i = s_i.theta
            U_i = s_i.U

            def inner_psi(t1: DBTuple) -> BoolRef:
                return Implies(
                    And(t1[U_i] == t[U_i], theta_i(**t1)),
                    And(theta(**t1), t1[U] == t[U])
                )

            psi_i = for_all_tuples("t1", schema, inner_psi)
            clauses.append(And(theta_i(**t), psi_i))

        return Implies(theta(**t), Or(clauses))

    expr = for_all_tuples("t", schema, inner)

    sol = Solver()
    sol.add(Not(expr))  # Check the satisfiability of its negation.

    if verbose:
        for assertion in sol.assertions():
            display(assertion)

    res = sol.check()
    if res == unsat:
        return True
    elif res == sat:
        if verbose:
            display(sol.model())
        return False
    else:
        assert False, "Z3 isn't sure"
