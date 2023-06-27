# Needed to annotate with a type that hasn't been defined yet.
from __future__ import annotations
from dataclasses import dataclass
from py_ecc import bn128
from typing import List, Union

F = bn128.FQ


@dataclass
class Const():
    c: F


@dataclass
class Var():
    v: str


@dataclass
class Sum():
    es: List[AExpr]


@dataclass
class Mul():
    es: List[AExpr]


@dataclass
class Neg():
    e: AExpr


@dataclass
class Pow():
    e: AExpr
    p: int


@dataclass
class AExpr():
    """Arithmetic Expression"""
    e: Const | Var | Sum | Mul | Neg | Pow

    def type_id(self: AExpr) -> int:
        match self.e:
            case Const(_):
                return 0
            case Var(_):
                return 1
            case Neg(_):
                return 2
            case Pow(_, _):
                return 3
            case Sum(_):
                return 4
            case Mul(_):
                return 5

    def __neg__(self: AExpr) -> AExpr:
        match self.e:
            case Neg(e):
                return AExpr(e)
            case _:
                return AExpr(Neg(self))

    def __rsub__(b: ToAExpr, a: ToAExpr) -> AExpr:
        return AExpr.__sub__(a, b)

    def __sub__(a: ToAExpr, b: ToAExpr) -> AExpr:
        (a, b) = (to_aexpr(a), to_aexpr(b))
        match (a.e, b.e):
            case (Sum(es), _):
                es = es + [AExpr(Neg(b))]
                return AExpr(Sum(es))
            case _:
                return AExpr(Sum([a, AExpr(Neg(b))]))

    def __radd__(b: ToAExpr, a: ToAExpr) -> AExpr:
        return AExpr.__add__(a, b)

    def __add__(a: ToAExpr, b: ToAExpr) -> AExpr:
        (a, b) = (to_aexpr(a), to_aexpr(b))
        match (a.e, b.e):
            # case (Const(c0), Const(c1)):
            #     return AExpr(Const(c0 + c1))
            case (Sum(es), _):
                es = es + [b]
                return AExpr(Sum(es))
            case (_, Sum(es)):
                es = [a] + es
                return AExpr(Sum(es))
            case _:
                return AExpr(Sum([a, b]))

    def __rmul__(b: ToAExpr, a: ToAExpr) -> AExpr:
        return AExpr.__mul__(a, b)

    def __mul__(a: ToAExpr, b: ToAExpr) -> AExpr:
        (a, b) = (to_aexpr(a), to_aexpr(b))
        match (a.e, b.e):
            # case (Const(c0), Const(c1)):
            #     return AExpr(Const(c0 * c1))
            case (Mul(es), _):
                es = es + [b]
                return AExpr(Mul(es))
            case (_, Mul(es)):
                es = [a] + es
                return AExpr(Mul(es))
            case _:
                return AExpr(Mul([a, b]))

    def is_terminal(self: AExpr) -> bool:
        match self.e:
            case Const(_) | Var(_) | Pow(_, _):
                return True
            case _:
                return False

    def is_mul_terminal(self: AExpr) -> bool:
        match self.e:
            case Const(_) | Var(_) | Mul(_) | Pow(_, _):
                return True
            case _:
                return False

    def fmt_ascii(self: AExpr) -> str:
        def fmt_exp(e: AExpr) -> str:
            parens = not e.is_terminal()
            result = ''
            if parens:
                result += '('
            result += e.fmt_ascii()
            if parens:
                result += ')'
            return result

        match self.e:
            case Neg(e):
                return '-' + fmt_exp(e)
            case Pow(e, p):
                return fmt_exp(e) + f'^{p}'
            case Const(c):
                # TODO: power of two as 2^x, long numbers as hex
                return f'{c}'
            case Var(v):
                return v
            case Sum(es):
                result = ''
                for i, e in enumerate(es):
                    neg = False
                    match e.e:
                        case Neg(ne):
                            neg = True
                            e = ne
                        case _:
                            pass
                    if i == 0:
                        if neg:
                            result += '-'
                    elif neg:
                        result += ' - '
                    else:
                        result += ' + '
                    result += fmt_exp(e)
                return result
            case Mul(es):
                result = ''
                for i, e in enumerate(es):
                    result += fmt_exp(e)
                    if i != len(es) - 1:
                        result += '*'
                return result

    def __str__(self: AExpr) -> str:
        return self.fmt_ascii()


ToAExpr = AExpr | str | int | F


@dataclass
class Comp():
    """Comparison between pair of nodes for equality/inequality"""
    pair: (LExpr, LExpr) | (AExpr, AExpr)


@dataclass
class And():
    es: List[LExpr]


@dataclass
class Or():
    es: List[LExpr]


@dataclass
class Not():
    e: LExpr


@dataclass
class Eq():
    c: Comp


@dataclass
class Neq():
    c: Comp


@dataclass
class LExpr():
    """Logical Expression"""
    e: And | Or | Not | Eq | Neq


@dataclass
class Assert():
    s: Cond | LExpr


@dataclass
class If():
    cond: LExpr
    true_e: Assert


@dataclass
class IfElse():
    cond: LExpr
    true_e: Assert
    false_e: Assert


@dataclass
class Switch():
    e: AExpr
    cases: List[Assert]


@dataclass
class Cond():
    """Condition"""
    c: If | IfElse | Switch


def to_aexpr(v: ToAExpr) -> AExpr:
    if isinstance(v, AExpr):
        return v
    elif isinstance(v, F):
        return AExpr(Const(v))
    elif isinstance(v, int):
        if v >= 0:
            return AExpr(Const(F(v)))
        else:
            return AExpr(Neg(AExpr(Const(F(-v)))))
    else:
        raise ValueError(f'type `{type(v)}` is not ToAExpr')


def main():
    def var(s: str) -> AExpr:
        return AExpr(Var(s))

    print(10 + var('a'))
    print(var('a') + 10)
    print(var('a') + 2 + 10)
    e = var('a') + 10
    print(e + var('b'))
    print(2 * e)
    print(e * 3)
    print(e - 3)
    print((var('a') + var('b')) * (2 - var('c')))


if __name__ == '__main__':
    main()
