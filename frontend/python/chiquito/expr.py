from __future__ import annotations
from typing import List
from dataclasses import dataclass

from chiquito.util import F


# pub enum Expr<F> {
#     Const(F),
#     Sum(Vec<Expr<F>>),
#     Mul(Vec<Expr<F>>),
#     Neg(Box<Expr<F>>),
#     Pow(Box<Expr<F>>, u32),
#     Query(Queriable<F>),
#     Halo2Expr(Expression<F>),
# }


@dataclass
class Expr:
    def __neg__(self: Expr) -> Neg:
        return Neg(self)

    def __add__(self: Expr, rhs: ToExpr) -> Sum:
        rhs = to_expr(rhs)
        return Sum([self, rhs])

    def __radd__(self: Expr, lhs: ToExpr) -> Sum:
        return Expr.__add__(lhs, self)

    def __sub__(self: Expr, rhs: ToExpr) -> Sum:
        rhs = to_expr(rhs)
        return Sum([self, Neg(rhs)])

    def __rsub__(self: Expr, lhs: ToExpr) -> Sum:
        return Expr.__sub__(lhs, self)

    def __mul__(self: Expr, rhs: ToExpr) -> Mul:
        rhs = to_expr(rhs)
        return Mul([self, rhs])

    def __rmul__(self: Expr, lhs: ToExpr) -> Mul:
        return Expr.__mul__(lhs, self)

    def __pow__(self: Expr, rhs: int) -> Pow:
        return Pow(self, rhs)


@dataclass
class Const(Expr):
    value: F

    def __str__(self: Const) -> str:
        return str(self.value)

    def __json__(self):
        return {"Const": self.value}


@dataclass
class Sum(Expr):
    exprs: List[Expr]

    def __str__(self: Sum) -> str:
        result = "("
        for i, expr in enumerate(self.exprs):
            if type(expr) is Neg:
                if i == 0:
                    result += "-"
                else:
                    result += " - "
            else:
                if i > 0:
                    result += " + "
            result += str(expr)
        result += ")"
        return result

    def __json__(self):
        return {"Sum": [expr.__json__() for expr in self.exprs]}

    def __add__(self: Sum, rhs: ToExpr) -> Sum:
        rhs = to_expr(rhs)
        return Sum(self.exprs + [rhs])

    def __radd__(self: Sum, lhs: ToExpr) -> Sum:
        return Sum.__add__(lhs, self)

    def __sub__(self: Sum, rhs: ToExpr) -> Sum:
        rhs = to_expr(rhs)
        return Sum(self.exprs + [Neg(rhs)])

    def __rsub__(self: Sum, lhs: ToExpr) -> Sum:
        return Sum.__sub__(lhs, self)


@dataclass
class Mul(Expr):
    exprs: List[Expr]

    def __str__(self: Mul) -> str:
        return "*".join([str(expr) for expr in self.exprs])

    def __json__(self):
        return {"Mul": [expr.__json__() for expr in self.exprs]}

    def __mul__(self: Mul, rhs: ToExpr) -> Mul:
        rhs = to_expr(rhs)
        return Mul(self.exprs + [rhs])

    def __rmul__(self: Mul, lhs: ToExpr) -> Mul:
        return Mul.__mul__(lhs, self)


@dataclass
class Neg(Expr):
    expr: Expr

    def __str__(self: Neg) -> str:
        return "(-" + str(self.expr) + ")"

    def __json__(self):
        return {"Neg": self.expr.__json__()}

    def __neg__(self: Neg) -> Expr:
        return self.expr


@dataclass
class Pow(Expr):
    expr: Expr
    pow: int

    def __str__(self: Pow) -> str:
        return str(self.expr) + "^" + str(self.pow)

    def __json__(self):
        return {"Pow": [self.expr.__json__(), self.pow]}


ToExpr = Expr | int | F


def to_expr(v: ToExpr) -> Expr:
    if isinstance(v, Expr):
        return v
    elif isinstance(v, int):
        if v >= 0:
            return Const(F(v))
        else:
            return Neg(Const(F(-v)))
    elif isinstance(v, F):
        return Const(v)
    else:
        raise TypeError(
            f"Type {type(v)} is not ToExpr (one of Expr, int, F, or Constraint)."
        )
