from __future__ import annotations
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import List, Dict, Optional

from chiquito.util import F, uuid
from chiquito.expr import Expr, Const, Neg, to_expr, ToExpr
from chiquito.query import StepTypeNext
from chiquito.chiquito_ast import ASTStepType, Lookup


class Typing(Enum):
    Unknown = auto()
    Boolean = auto()
    AntiBooly = auto()


@dataclass
class Constraint:
    annotation: str
    expr: Expr
    typing: Typing

    def from_expr(
        expr: Expr,
    ) -> Constraint:  # Cannot call function `from`, a reserved keyword in Python.
        annotation: str = str(expr)
        if isinstance(expr, StepTypeNext):
            return Constraint(annotation, expr, Typing.Boolean)
        else:
            return Constraint(annotation, expr, Typing.Unknown)

    def __str__(self: Constraint) -> str:
        return self.annotation


def cb_and(
    inputs: List[ToConstraint],
) -> Constraint:  # Cannot call function `and`, a reserved keyword in Python
    inputs = [to_constraint(input) for input in inputs]
    annotations: List[str] = []
    expr = Const(F(1))
    for constraint in inputs:
        if constraint.typing == Typing.Boolean or constraint.typing == Typing.Unknown:
            annotations.append(constraint.annotation)
            expr = expr * constraint.expr
        else:
            raise ValueError(
                f"Expected Boolean or Unknown constraint, got AntiBooly (constraint: {constraint.annotation})"
            )
    return Constraint(f"({' AND '.join(annotations)})", expr, Typing.Boolean)


def cb_or(
    inputs: List[ToConstraint],
) -> Constraint:  # Cannot call function `or`, a reserved keyword in Python
    inputs = [to_constraint(input) for input in inputs]
    annotations: List[str] = []
    exprs: List[Expr] = []
    for constraint in inputs:
        if constraint.typing == Typing.Boolean or constraint.typing == Typing.Unknown:
            annotations.append(constraint.annotation)
            exprs.append(constraint.expr)
        else:
            raise ValueError(
                f"Expected Boolean or Unknown constraint, got AntiBooly (constraint: {constraint.annotation})"
            )
    result: Constraint = Constraint.cb_not(
        Constraint.cb_and([Constraint.cb_not(expr) for expr in exprs])
    )
    return Constraint(f"({' OR '.join(annotations)})", result.expr, Typing.Boolean)


def xor(lhs: ToConstraint, rhs: ToConstraint) -> Constraint:
    (lhs, rhs) = (to_constraint(lhs), to_constraint(rhs))
    if (lhs.typing == Typing.Boolean or lhs.typing == Typing.Unknown) and (
        rhs.typing == Typing.Boolean or rhs.typing == Typing.Unknown
    ):
        return Constraint(
            f"({lhs.annotation} XOR {rhs.annotation})",
            lhs.expr + rhs.expr - F(2) * lhs.expr * rhs.expr,
            Typing.Boolean,
        )
    else:
        raise ValueError(
            f"Expected Boolean or Unknown constraints, got AntiBooly in one of lhs or rhs constraints (lhs constraint: {lhs.annotation}) (rhs constraint: {rhs.annotation})"
        )


def eq(lhs: ToConstraint, rhs: ToConstraint) -> Constraint:
    (lhs, rhs) = (to_constraint(lhs), to_constraint(rhs))
    return Constraint(
        f"({lhs.annotation} == {rhs.annotation})",
        lhs.expr - rhs.expr,
        Typing.AntiBooly,
    )


def select(
    selector: ToConstraint, when_true: ToConstraint, when_false: ToConstraint
) -> Constraint:
    (selector, when_true, when_false) = (
        to_constraint(selector),
        to_constraint(when_true),
        to_constraint(when_false),
    )
    if selector.typing == Typing.AntiBooly:
        raise ValueError(
            f"Expected Boolean or Unknown selector, got AntiBooly (selector: {selector.annotation})"
        )
    return Constraint(
        f"if({selector.annotation})then({when_true.annotation})else({when_false.annotation})",
        selector.expr * when_true.expr + (F(1) - selector.expr) * when_false.expr,
        when_true.typing if when_true.typing == when_false.typing else Typing.Unknown,
    )


def when(selector: ToConstraint, when_true: ToConstraint) -> Constraint:
    (selector, when_true) = (to_constraint(selector), to_constraint(when_true))
    if selector.typing == Typing.AntiBooly:
        raise ValueError(
            f"Expected Boolean or Unknown selector, got AntiBooly (selector: {selector.annotation})"
        )
    return Constraint(
        f"if({selector.annotation})then({when_true.annotation})",
        selector.expr * when_true.expr,
        when_true.typing,
    )


def unless(selector: ToConstraint, when_false: ToConstraint) -> Constraint:
    (selector, when_false) = (to_constraint(selector), to_constraint(when_false))
    if selector.typing == Typing.AntiBooly:
        raise ValueError(
            f"Expected Boolean or Unknown selector, got AntiBooly (selector: {selector.annotation})"
        )
    return Constraint(
        f"unless({selector.annotation})then({when_false.annotation})",
        (F(1) - selector.expr) * when_false.expr,
        when_false.typing,
    )


def cb_not(
    constraint: ToConstraint,
) -> Constraint:  # Cannot call function `not`, a reserved keyword in Python
    constraint = to_constraint(constraint)
    if constraint.typing == Typing.AntiBooly:
        raise ValueError(
            f"Expected Boolean or Unknown constraint, got AntiBooly (constraint: {constraint.annotation})"
        )
    return Constraint(
        f"NOT({constraint.annotation})", F(1) - constraint.expr, Typing.Boolean
    )


def isz(constraint: ToConstraint) -> Constraint:
    constraint = to_constraint(constraint)
    return Constraint(
        f"0 == {constraint.annotation}", constraint.expr, Typing.AntiBooly
    )


def if_next_step(step_type: ASTStepType, constraint: ToConstraint) -> Constraint:
    constraint = to_constraint(constraint)
    return Constraint(
        f"if(next step is {step_type.annotation})then({constraint.annotation})",
        StepTypeNext(step_type) * constraint.expr,
        constraint.typing,
    )


def next_step_must_be(step_type: ASTStepType) -> Constraint:
    return Constraint(
        f"next step must be {step_type.annotation}",
        Constraint.cb_not(StepTypeNext(step_type)),
        Typing.AntiBooly,
    )


def next_step_must_not_be(step_type: ASTStepType) -> Constraint:
    return Constraint(
        f"next step must not be {step_type.annotation}",
        StepTypeNext(step_type),
        Typing.AntiBooly,
    )


def rlc(exprs: List[ToExpr], randomness: Expr) -> Expr:
    if len(exprs) > 0:
        exprs: List[Expr] = [to_expr(expr) for expr in exprs].reverse()
        init: Expr = exprs[0]
        for expr in exprs[1:]:
            init = init * randomness + expr
        return init
    else:
        return Expr(Const(F(0)))


def lookup() -> InPlaceLookupBuilder:
    return InPlaceLookupBuilder()


def table() -> LookupTable:
    return LookupTable()


ToConstraint = Constraint | Expr | int | F


def to_constraint(v: ToConstraint) -> Constraint:
    if isinstance(v, Constraint):
        return v
    elif isinstance(v, Expr):
        if isinstance(v, StepTypeNext):
            return Constraint(str(v), v, Typing.Boolean)
        else:
            return Constraint(str(v), v, Typing.Unknown)
    elif isinstance(v, int):
        if v >= 0:
            return to_constraint(Const(F(v)))
        else:
            return to_constraint(Neg(Const(F(-v))))
    elif isinstance(v, F):
        return to_constraint(Const(v))
    else:
        raise TypeError(
            f"Type `{type(v)}` is not ToConstraint (one of Constraint, Expr, int, or F)."
        )


@dataclass
class LookupTableRegistry:
    tables: Dict[int, LookupTable] = field(default_factory=dict)

    def add(self: LookupTableRegistry, table: LookupTable):
        self.tables[table.uuid] = table

    def get(self: LookupTableRegistry, uuid: int) -> LookupTable:
        return self.tables[uuid]


@dataclass
class LookupTable:
    uuid: int = 0
    dest: List[Expr] = field(default_factory=list)

    def __init__(self: LookupTable):
        self.uuid: int = uuid()
        self.dest = []

    def add(self: LookupTable, expr: ToExpr) -> LookupTable:
        self.dest.append(to_expr(expr))
        return self

    def apply(self: LookupTable, constraint: ToConstraint) -> LookupTableBuilder:
        return LookupTableBuilder(self.uuid).apply(constraint)

    def when(self: LookupTable, enable: ToConstraint) -> LookupTableBuilder:
        return LookupTableBuilder(self.uuid).when(enable)


@dataclass
class LookupTableBuilder:
    uuid: int
    src: List[Constraint] = field(default_factory=list)
    enable: Optional[Constraint] = None

    def __init__(self: LookupTableBuilder, uuid: int):
        self.uuid: int = uuid

    def apply(self: LookupTableBuilder, constraint: ToConstraint) -> LookupTableBuilder:
        self.src.append(to_constraint(constraint))
        return self

    def when(self: LookupTableBuilder, enable: ToConstraint) -> LookupTableBuilder:
        if self.enable is not None:
            raise ValueError("LookupTableBuilder: when() can only be called once.")
        self.enable = to_constraint(enable)
        return self

    def build(self: LookupTableBuilder, step_type: StepType) -> Lookup:
        table = step_type.tables.get(self.id)
        if self.src.len() != table.dest.len():
            raise ValueError(
                "LookupTableBuilder: build() has different number of source columns and destination columns."
            )

        lookup = Lookup()

        if self.enable is not None:
            lookup.enable(self.enable.annotation, self.enable.expr)

        for i in range(self.src.len()):
            lookup.add(self.src[i].annotation, self.src[i].expr, table.dest[i])

        return lookup


@dataclass
class InPlaceLookupBuilder:
    lookup: Lookup = field(default_factory=Lookup)

    def build(self: InPlaceLookupBuilder, _: StepType) -> Lookup:
        return self.lookup

    def add(
        self: InPlaceLookupBuilder, constraint: ToConstraint, expression: ToExpr
    ) -> InPlaceLookupBuilder:
        constraint = to_constraint(constraint)
        self.lookup.add(constraint.annotation, constraint.expr, to_expr(expression))
        return self

    def enable(
        self: InPlaceLookupBuilder, enable: ToConstraint
    ) -> InPlaceLookupBuilder:
        enable = to_constraint(enable)
        self.lookup.enable(enable.annotation, enable.expr)
        return self
