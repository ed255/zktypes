# Needed to annotate with a type that hasn't been defined yet.
from __future__ import annotations

from copy import deepcopy
from math import ceil
from functools import reduce
from itertools import chain
from enum import Enum, auto
from varname import varname  # type: ignore
from dataclasses import dataclass, field
from py_ecc import bn128
from typing import List, Union, Optional, Callable, Any, Self, TypeVar, Generic, Tuple, Dict, Iterator
from typing_extensions import Protocol
import inspect

F = bn128.FQ


class SupportsFmtAscii(Protocol):
    def fmt_ascii(self) -> str:
        ...


class SupportsVars(Protocol):
    def vars(self) -> List[Any]:
        ...


class SupportsEval(Protocol):
    def var_eval(self, Signal) -> F:
        ...

    def lvar_eval(self, Signal) -> bool:
        ...


def f_fmt_ascii(c: F) -> str:
    return i_fmt_ascii(c.n)


def i_fmt_ascii(c: int) -> str:
    sign = ""
    if c < 0:
        c = -c
        sign = "-"
    c_bin = bin(c)[2:]
    c_bin_p1 = bin(c+1)[2:]
    if len(c_bin) >= 8 and c_bin.count("1") == 1:
        return f"{sign}2^{len(c_bin)-1}"
    if len(c_bin_p1) >= 8 and c_bin_p1.count("1") == 1:
        return f"{sign}2^{len(c_bin_p1)-1}-1"
    elif len(c_bin) >= 16:
        return f"{sign}0x{c:02x}"
    else:
        return f"{c}"


V = TypeVar("V", bound=SupportsFmtAscii)


@dataclass
class StrVar:
    s: str

    def __hash__(self):
        return self.s.__hash__()

    def fmt_ascii(self) -> str:
        return self.s


@dataclass
class AVar():
    """Arithmetic Variable"""
    inner: Var
    component: Component

    def v(self) -> F:
        # TODO
        return F(0)

    def signal(self) -> Signal:
        return self.inner

    def fmt_ascii(self) -> str:
        return self.inner.fmt_ascii()

    def __neg__(self: AVar) -> AExpr:
        return AExpr(self).__neg__()

    def __rsub__(b: ToAExpr, a: AVar) -> AExpr:
        return to_aexpr(a).__sub__(b)

    def __sub__(a: AVar, b: ToAExpr) -> AExpr:
        return AExpr(a).__sub__(b)

    def __radd__(b: ToAExpr, a: AVar) -> AExpr:
        return to_aexpr(a).__add__(b)

    def __add__(a: AVar, b: ToAExpr) -> AExpr:
        return AExpr(a).__add__(b)

    def __rmul__(b: ToAExpr, a: AVar) -> AExpr:
        return to_aexpr(a).__mul__(b)

    def __mul__(a: AVar, b: ToAExpr) -> AExpr:
        return AExpr(a).__mul__(b)

    def __pow__(a: AVar, b: int) -> AExpr:
        return AExpr(a).__pow__(b)

    def __req__(b: ToAExpr, a: AVar) -> LExpr:
        return AExpr(a).__eq__(b)

    def __eq__(a: AVar, b: ToAExpr) -> LExpr:  # type: ignore
        return AExpr(a).__eq__(b)

    def __rne__(b: ToAExpr, a: AVar) -> LExpr:
        return AExpr(a).__ne__(b)

    def __ne__(a: AVar, b: ToAExpr) -> LExpr:  # type: ignore
        return AExpr(a).__ne__(b)




@dataclass
class Const:
    c: F


@dataclass
class Sum:
    es: List[AExpr]


@dataclass
class Mul:
    es: List[AExpr]


@dataclass
class Neg:
    e: AExpr


@dataclass
class Pow:
    e: AExpr
    p: int


@dataclass
class AExpr:
    """Arithmetic Expression"""

    e: Const | AVar | Sum | Mul | Neg | Pow

    def case_id(self: AExpr) -> int:
        match self.e:
            case Const(_):
                return 0
            case AVar(_, _):
                return 1
            case Neg(_):
                return 2
            case Pow(_, _):
                return 3
            case Sum(_):
                return 4
            case Mul(_):
                return 5

    def is_var(self) -> bool:
        match self.e:
            case AVar(_, _):
                return True
            case _:
                return False

    def as_var(self) -> Optional[Any]:
        match self.e:
            case AVar(v, _):
                return v
            case _:
                return None

    def vars(self) -> List[Any]:
        match self.e:
            case Neg(e):
                return e.vars()
            case Pow(e, _):
                return e.vars()
            case Const(_):
                return []
            case AVar(v, _):
                return [v]
            case Sum(es):
                return list(chain(*[e.vars() for e in es]))
            case Mul(es):
                return list(chain(*[e.vars() for e in es]))


    def __neg__(self: AExpr) -> AExpr:
        match self.e:
            case Neg(e):
                return e
            case _:
                return AExpr(Neg(self))

    def __rsub__(b: ToAExpr, a: AExpr) -> AExpr:
        return AExpr.__sub__(a, b)

    def __sub__(a: AExpr, b: ToAExpr) -> AExpr:
        b = to_aexpr(b)
        match (a.e, b.e):
            case (Sum(es), _):
                es = es + [AExpr(Neg(b))]
                return AExpr(Sum(es))
            case _:
                return AExpr(Sum([a, AExpr(Neg(b))]))

    def __radd__(b: ToAExpr, a: AExpr) -> AExpr:
        return AExpr.__add__(a, b)

    def __add__(a: AExpr, b: ToAExpr) -> AExpr:
        b = to_aexpr(b)
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

    def __rmul__(b: ToAExpr, a: AExpr) -> AExpr:
        return AExpr.__mul__(a, b)

    def __mul__(a: AExpr, b: ToAExpr) -> AExpr:
        b = to_aexpr(b)
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

    def __pow__(a: AExpr, b: int) -> AExpr:
        return AExpr(Pow(a, b))

    def __truediv__(a: AExpr, b: int) -> AExpr:
        b_inv = F(1) / b
        return a * b_inv

    def __req__(b: ToAExpr, a: AExpr) -> LExpr:
        return AExpr.__eq__(a, b)

    def __eq__(a: AExpr, b: ToAExpr) -> LExpr:  # type: ignore
        b = to_aexpr(b)
        return LExpr(Eq(AExprPair(a, b)))

    def __rne__(b: ToAExpr, a: AExpr) -> LExpr:
        return AExpr.__ne__(a, b)

    def __ne__(a: AExpr, b: ToAExpr) -> LExpr:  # type: ignore
        b = to_aexpr(b)
        return LExpr(Neq(AExprPair(a, b)))

    def type_eval(self) -> StaticBound:
        match self.e:
            case Neg(e):
                return -e.type_eval()
            case Pow(e, p):
                if p == 0:
                    return StaticBound(1, 1)
                bound = e.type_eval()
                for _ in range(1, p):
                    bound = bound * bound
                return bound
            case Const(c):
                return StaticBound(c, c)
            case AVar(v, _):
                return v.inferred
            case Sum(es):
                bound = es[0].type_eval()
                for e in es[1:]:
                    b = e.type_eval()
                    bound = bound + b
                return bound
            case Mul(es):
                bound = es[0].type_eval()
                for e in es[1:]:
                    b = e.type_eval()
                    bound = bound * b
                return bound

    def eval(self, vars: SupportsEval) -> F:
        match self.e:
            case Neg(e):
                return -e.eval(vars)
            case Pow(e, p):
                return e.eval(vars) ** p
            case Const(c):
                return c
            case AVar(v, _):
                return vars.var_eval(v)
            case Sum(es):
                return sum([e.eval(vars) for e in es], start=F(0))
            case Mul(es):
                return reduce(lambda x, y: x * y, [e.eval(vars) for e in es], F(1))

    def is_terminal(self: AExpr) -> bool:
        match self.e:
            case Const(_) | AVar(_, _) | Pow(_, _):
                return True
            case _:
                return False

    def is_mul_terminal(self: AExpr) -> bool:
        match self.e:
            case Const(_) | AVar(_, _) | Mul(_) | Pow(_, _):
                return True
            case _:
                return False

    def fmt_ascii(self: AExpr) -> str:
        def fmt_exp(e: AExpr) -> str:
            parens = not e.is_mul_terminal()
            result = ""
            if parens:
                result += "("
            result += e.fmt_ascii()
            if parens:
                result += ")"
            return result

        match self.e:
            case Neg(e):
                return "-" + fmt_exp(e)
            case Pow(e, p):
                return fmt_exp(e) + f"^{p}"
            case Const(c):
                return f_fmt_ascii(c)
            case AVar(_, _) as e:
                return e.fmt_ascii()
            case Sum(es):
                result = ""
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
                            result += "-"
                    elif neg:
                        result += " - "
                    else:
                        result += " + "
                    result += fmt_exp(e)
                return result
            case Mul(es):
                result = ""
                for i, e in enumerate(es):
                    result += fmt_exp(e)
                    if i != len(es) - 1:
                        result += "*"
                return result

    def __str__(self: AExpr) -> str:
        return self.fmt_ascii()


ToAExpr = AExpr | AVar | str | int | F


@dataclass
class AExprPair:
    lhs: AExpr
    rhs: AExpr


@dataclass
class LExprPair:
    lhs: LExpr
    rhs: LExpr


@dataclass
class LVar(Generic[V]):
    """Logical Variable"""
    inner: Var
    component: Component

    def fmt_ascii(self) -> str:
        return self.inner.fmt_ascii()

    def v(self) -> bool:
        # TODO
        return False

    def signal(self) -> Signal:
        return self.inner

    def __eq__(a: LVar, b: ToLExpr) -> LExpr:  # type: ignore
        """called with `==`"""
        return LExpr(a).__eq__(b)

    def __req__(b: ToLExpr, a: LVar) -> LExpr:  # type: ignore
        return LExpr(a).__eq__(b)

    def __ne__(a: LVar, b: ToLExpr) -> LExpr:  # type: ignore
        """called with `!=`"""
        return LExpr(a).__ne__(b)

    def __rne__(b: ToLExpr, a: LVar) -> LExpr:  # type: ignore
        return LExpr(a).__ne__(b)

    def __invert__(self: LVar) -> LExpr:
        """not.  Called with `~`"""
        return LExpr(self).__invert__()

    def __and__(a: LVar, b: ToLExpr) -> LExpr:
        """Called with `&`"""
        return LExpr(a).__and__(b)

    def __rand__(b: ToLExpr, a: LVar) -> LExpr:
        return LExpr(a).__and__(b)

    def __or__(a: LVar, b: ToLExpr) -> LExpr:
        """Called with `|`"""
        return LExpr(a).__or__(b)

    def __ror__(b: ToLExpr, a: LVar) -> LExpr:
        return LExpr(a).__or__(b)


@dataclass
class And:
    es: List[LExpr]


@dataclass
class Or:
    es: List[LExpr]


@dataclass
class Not:
    e: LExpr


@dataclass
class Eq:
    pair: AExprPair | LExprPair


@dataclass
class Neq:
    pair: AExprPair | LExprPair


@dataclass
class LExpr:
    """Logical Expression"""

    e: LVar | And | Or | Not | Eq | Neq

    def is_var(self) -> bool:
        match self.e:
            case LVar(_, _):
                return True
            case _:
                return False

    def as_var(self) -> Optional[Any]:
        match self.e:
            case LVar(v, _):
                return v
            case _:
                return None

    def vars(self) -> List[Any]:
        match self.e:
            case LVar(v, _):
                return [v]
            case And(es):
                return list(chain(*[e.vars() for e in es]))
            case Or(es):
                return list(chain(*[e.vars() for e in es]))
            case Not(e):
                return e.vars()
            case Eq(pair):
                match pair:
                    case AExprPair(lhs, rhs):
                        return lhs.vars() + rhs.vars()
                    case LExprPair(lhs, rhs):
                        return lhs.vars() + rhs.vars()
            case Neq(pair):
                match pair:
                    case AExprPair(lhs, rhs):
                        return lhs.vars() + rhs.vars()
                    case LExprPair(lhs, rhs):
                        return lhs.vars() + rhs.vars()

    def __eq__(a: LExpr, b: ToLExpr) -> LExpr:  # type: ignore
        """called with `==`"""
        b = to_lexpr(b)
        return LExpr(Eq(LExprPair(a, b)))

    def __ne__(a: LExpr, b: ToLExpr) -> LExpr:  # type: ignore
        """called with `!=`"""
        b = to_lexpr(b)
        return LExpr(Neq(LExprPair(a, b)))

    def __invert__(self: LExpr) -> LExpr:
        """not.  Called with `~`"""
        return LExpr(Not(self))

    def __and__(a: LExpr, b: ToLExpr) -> LExpr:
        """Called with `&`"""
        b = to_lexpr(b)
        match (a.e, b.e):
            case (And(es), _):
                es = es + [b]
                return LExpr(And(es))
            case (_, And(es)):
                es = es + [b]
                return LExpr(And(es))
            case _:
                return LExpr(And([a, b]))

    def __or__(a: LExpr, b: ToLExpr) -> LExpr:
        """Called with `|`"""
        b = to_lexpr(b)
        match (a.e, b.e):
            case (Or(es), _):
                es = es + [b]
                return LExpr(Or(es))
            case (_, Or(es)):
                es = es + [b]
                return LExpr(Or(es))
            case _:
                return LExpr(Or([a, b]))

    def eval(self, vars: SupportsEval) -> bool:
        match self.e:
            case LVar(v, _):
                return vars.lvar_eval(v)
            case And(es):
                return reduce(lambda x, y: x and y, [e.eval(vars) for e in es], True)
            case Or(es):
                return reduce(lambda x, y: x or y, [e.eval(vars) for e in es], False)
            case Not(e):
                return not e.eval(vars)
            case Eq(pair):
                match pair:
                    case AExprPair(lhs, rhs):
                        return lhs.eval(vars) == rhs.eval(vars)
                    case LExprPair(lhs, rhs):
                        return lhs.eval(vars) == rhs.eval(vars)
            case Neq(pair):
                match pair:
                    case AExprPair(lhs, rhs):
                        return lhs.eval(vars) != rhs.eval(vars)
                    case LExprPair(lhs, rhs):
                        return lhs.eval(vars) != rhs.eval(vars)

    def is_terminal(self: LExpr) -> bool:
        match self.e:
            case LVar(_, _) | Not(_):
                return True
            case _:
                return False

    def fmt_ascii(self: LExpr) -> str:
        def fmt_exp(e: LExpr) -> str:
            parens = not e.is_terminal()
            result = ""
            if parens:
                result += "("
            result += e.fmt_ascii()
            if parens:
                result += ")"
            return result

        match self.e:
            case LVar(_, _) as e:
                return e.fmt_ascii()
            case And(es):
                return " and ".join([fmt_exp(e) for e in es])
            case Or(es):
                return " or ".join([fmt_exp(e) for e in es])
            case Not(e):
                return "not(" + fmt_exp(e) + ")"
            case Eq(pair):
                match pair:
                    case AExprPair(lhs, rhs):
                        return lhs.fmt_ascii() + " == " + rhs.fmt_ascii()
                    case LExprPair(lhs, rhs):
                        return fmt_exp(lhs) + " == " + fmt_exp(rhs)
            case Neq(pair):
                match pair:
                    case AExprPair(lhs, rhs):
                        return lhs.fmt_ascii() + " != " + rhs.fmt_ascii()
                    case LExprPair(lhs, rhs):
                        return fmt_exp(lhs) + " != " + fmt_exp(rhs)

    def __str__(self: LExpr) -> str:
        return self.fmt_ascii()


# ToLExpr = LExpr | LVar | bool
ToLExpr = LExpr | LVar


@dataclass
class RangeCheck:
    var: AVar
    bound: StaticBound

    def __str__(self) -> str:
        return f"{self.var.fmt_ascii()} in {self.bound}"


@dataclass
class Assert:
    s: Cond | LExpr | RangeCheck
    id: int = -1
    frame: Optional[inspect.FrameInfo] = None

    def __str__(self: Assert) -> str:
        return self.s.__str__()

    def vars(self) -> List[Any]:
        match self.s:
            case Cond(c):
                match c:
                    case If(cond, true_e):
                        return cond.vars() + true_e.vars()
                    case IfElse(cond, true_e, false_e):
                        return cond.vars() + true_e.vars() + false_e.vars()
                    case Switch(_, _):
                        raise NotImplementedError
            case LExpr(_) as e:
                return e.vars()
            case RangeCheck(v, _):
                return [v]

    def verify(self, vars: SupportsEval) -> bool:
        match self.s:
            case Cond(_) as a:
                return a.verify(vars)
            case LExpr(_) as e:
                return e.eval(vars)
            case RangeCheck(var, bound):
                v: F = vars.var_eval(var.signal())
                assert len(bound.intervals) == 1
                interval = bound.intervals[0]
                return interval[0] <= v.n and v.n <= interval[1]


@dataclass
class If:
    cond: LExpr
    true_e: Assert


@dataclass
class IfElse:
    cond: LExpr
    true_e: Assert
    false_e: Assert


@dataclass
class Switch:
    e: AExpr
    cases: List[Assert]


@dataclass
class Cond:
    """Condition"""

    c: If | IfElse | Switch

    def fmt_ascii(self: Cond, indent: int) -> List[str]:
        def spaces(indent: int) -> str:
            return " " * 2 * indent

        def fmt_assert(a: Assert, indent: int) -> List[str]:
            lines = []
            match a.s:
                case Cond(_) as c:
                    lines += c.fmt_ascii(indent)
                case LExpr(_) as e:
                    lines.append(spaces(indent) + e.fmt_ascii())
            return lines

        lines = []
        match self.c:
            case If(cond, true_e):
                lines.append("if " + cond.fmt_ascii() + ":")
                lines += fmt_assert(true_e, 1)
            case IfElse(cond, true_e, false_e):
                lines.append("if " + cond.fmt_ascii() + ":")
                lines += fmt_assert(true_e, 1)
                lines.append("else:")
                lines += fmt_assert(false_e, 1)
            case Switch(_, _):
                raise NotImplementedError
        return [spaces(indent) + line for line in lines]

    def __str__(self: Cond) -> str:
        return "\n".join(self.fmt_ascii(0))

    def verify(self, vars: SupportsEval) -> bool:
        match self.c:
            case If(cond, true_e):
                if cond.eval(vars):
                    return true_e.verify(vars)
                else:
                    return True
            case IfElse(cond, true_e, false_e):
                if cond.eval(vars):
                    return true_e.verify(vars)
                else:
                    return false_e.verify(vars)
            case Switch(_, _):
                raise NotImplementedError


def to_aexpr(v: ToAExpr) -> AExpr:
    if isinstance(v, AExpr):
        return v
    if isinstance(v, AVar):
        return AExpr(v)
    elif isinstance(v, F):
        return AExpr(Const(v))
    elif isinstance(v, int):
        if v >= 0:
            return AExpr(Const(F(v)))
        else:
            return AExpr(Neg(AExpr(Const(F(-v)))))
    else:
        raise ValueError(f"type `{type(v)}` is not ToAExpr")


def to_lexpr(v: ToLExpr) -> LExpr:
    if isinstance(v, LExpr):
        return v
    if isinstance(v, LVar):
        return LExpr(v)
    # elif isinstance(v, bool):
    #     return AExpr(Const(v))
    else:
        raise ValueError(f"type `{type(v)}` is not ToLExpr")


q = F(-1).n + 1


class StaticBound:
    """Bound an expression between [interval[0], interval[1]]"""
    intervals: List[Tuple[int, int]]

    def __init__(self, start: int | F, end: int | F):
        if isinstance(start, F):
            start = start.n
        if isinstance(end, F):
            end = end.n
        assert start <= end
        self.intervals = [(start, end)]

    @classmethod
    def from_intervals(cls, intervals: List[Tuple[int, int]]) -> StaticBound:
        bound = StaticBound(0, 0)
        bound.intervals = intervals
        return bound

    @classmethod
    def default(cls) -> StaticBound:
        return StaticBound(F(0), F(-1))

    def overflow(self) -> bool:
        for interval in self.intervals:
            if interval[0] < 0 or interval[1] > F(-1).n:
                return True
        return False

    def __add__(a: StaticBound, b: StaticBound) -> StaticBound:
        intervals = []
        for interval_a in a.intervals:
            for interval_b in b.intervals:
                start = interval_a[0] + interval_b[0]
                end = interval_a[1] + interval_b[1]
                intervals.append((start, end))
        return StaticBound.from_intervals(intervals)._clean()

    def __mul__(a: StaticBound, b: StaticBound) -> StaticBound:
        intervals = []
        for interval_a in a.intervals:
            for interval_b in b.intervals:
                start = interval_a[0] * interval_b[0]
                end = interval_a[1] * interval_b[1]
                intervals.append((start, end))
        return StaticBound.from_intervals(intervals)._clean()

    def __neg__(self: StaticBound) -> StaticBound:
        intervals = []
        for interval_a in self.intervals:
            end = -interval_a[0]
            start = -interval_a[1]
            intervals.append((start, end))
        intervals = list(reversed(intervals))
        return StaticBound.from_intervals(intervals)._clean()

    def _clean(self: StaticBound) -> StaticBound:
        new = [self.intervals[0]]
        for interval in self.intervals[1:]:
            if interval[1] < interval[0]:
                raise ValueError(f"Inverted interval {interval}")
            # If next interval overlaps previous one, merge them
            if interval[0] < new[-1][1]:
                new[-1] = (new[-1][0], interval[1])
            else:
                new.append(interval)
        new2 = []
        for interval in new:
            # Discard intervals outside of [- 2 * q, 3 * q - 1]
            # Clip intervals that overlap [- 2 * q, 3 * q - 1]
            if interval[1] < - 2 * q:
                continue
            elif interval[0] >= 3 * q - 1:
                continue
            elif interval[0] < - 2 * q:
                interval = (-2 * q, interval[1])
            elif interval[1] >= 3 * q - 1:
                interval = (interval[0], 3 * q - 1)
            new2.append(interval)
        self.intervals = new2
        return self


    def overlap(self: StaticBound, other: StaticBound) -> Tuple[StaticBound, bool]:
        # print(f"Begin overlap between {self} and {other}")
        if self.intervals == other.intervals:
            return self, False

        def cycle(a: Tuple[int, int], n: int) -> Tuple[int, int]:
            return (a[0] + n * q, a[1] + n * q)

        def overlap_intervals(a: Tuple[int, int], b: Tuple[int, int]) -> Tuple[int, int]:
            start = max(a[0], b[0])
            end = min(a[1], b[1])
            return (start, end)

        intervals = []
        for interval_a in self.intervals:
            for interval_b in other.intervals:
                a = cycle(interval_a, int(-ceil(interval_b[0] - interval_a[0])/q))
                while True:
                    overlap = overlap_intervals(a, interval_b)
                    if overlap[0] <= overlap[1]:
                        intervals.append(overlap)
                        # print(f"DBG A {overlap}")
                    a = cycle(a, 1)
                    if a[0] > interval_b[1]:
                        break
        for interval_a in other.intervals:
            for interval_b in self.intervals:
                a = cycle(interval_a, int(-ceil(interval_b[0] - interval_a[0])/q))
                while True:
                    overlap = overlap_intervals(a, interval_b)
                    if overlap[0] <= overlap[1]:
                        intervals.append(overlap)
                        # print(f"DBG B {overlap}")
                    a = cycle(a, 1)
                    if a[0] > interval_b[1]:
                        break
        # print(f"DBG C {intervals}")
        intervals.sort(key=lambda interval: interval[0])
        new = StaticBound.from_intervals(intervals)
        new._clean()
        update = self.intervals != new.intervals
        # if update:
        #     print(f"DBG {self.intervals} -> {new.intervals}")
        return (new, update)

    def type_check(self, type: StaticBound) -> bool:
        assert len(type.intervals) == 1
        type_interval = type.intervals[0]
        for interval in self.intervals:
            if interval[0] < type_interval[0] or interval[1] > type_interval[1]:
                return False
        return True

    def __str__(self) -> str:
        s = ""
        for (i, interval) in enumerate(self.intervals):
            if i != 0:
                s += ", "
            start = i_fmt_ascii(interval[0])
            end = i_fmt_ascii(interval[1])
            s += f"[{start}, {end}]"
        return f"{{{s}}}"


@dataclass
class Type:
    name: str
    t: StaticBound

    @classmethod
    def Bound(cls, start: int | F, end: int | F, name: Optional[str] = None):
        if name is None:
            name = varname()
        return cls(name, StaticBound(start, end))

    @classmethod
    def Any(cls):
        return cls("Any", StaticBound(F(0), F(-1)))


StaticBoundDefault = StaticBound.default()

@dataclass
class Signal:
    name: str
    fullname: str
    id: int
    frame: inspect.FrameInfo
    type: Optional[Type] = None
    inferred: StaticBound = StaticBoundDefault
    logical: bool = False

    def __post_init__(self):
        self.inferred = deepcopy(self.inferred)
        self.type = deepcopy(self.type)

    def fmt_ascii(self) -> str:
        return self.name


Var = Signal


InputOutput = AVar | LVar | List[AVar | LVar] | SupportsVars


def io_list(io: InputOutput) -> List[Signal]:
    signals: List[Signal] = []
    match io:
        case AVar(_, _) as v:
            signals = [v.signal()]
        case LVar(_, _) as v:
            signals = [v.signal()]
        case [*_] as vs:
            signals = [v.signal() for v in vs]
        case _:
            signals = [v.signal() for v in io.vars()]  # type: ignore
    return signals


class IO(Enum):
    IN = auto()
    OUT = auto()


class ComponentState(Enum):
    STARTED = auto()
    FINALIZED = auto()
    CONNECTED = auto()
    WITNESS_ASSIGNED = auto()


@dataclass
class AssignmentComponent:
    component: Component


@dataclass
class AssignmentEq:
    assert_id: int


@dataclass
class AssignmentManual:
    signal_id: int
    fn: Any


@dataclass
class Assignment:
    a: AssignmentComponent | AssignmentEq | AssignmentManual


@dataclass
class VarNotFoundError(Exception):
    v: Any


@dataclass
class Vars:
    """Hold variable assignments by id, resolve them by Signal.  Implements SupportsEval"""
    var_map: Dict[int, F] = field(default_factory=dict)
    lvar_map: Dict[int, bool] = field(default_factory=dict)

    def set(self, signal: Signal, value: bool | int | F):
        if signal.logical:
            assert isinstance(value, bool)
            self.lvar_map[signal.id] = value
        else:
            if isinstance(value, int):
                value = F(value)
            assert isinstance(value, F)
            self.var_map[signal.id] = value

    def var_eval(self, signal: Signal) -> F:
        assert not signal.logical
        try:
            return self.var_map[signal.id]
        except KeyError:
            raise VarNotFoundError(signal.id)

    def lvar_eval(self, signal: Signal) -> bool:
        assert signal.logical
        try:
            return self.lvar_map[signal.id]
        except KeyError:
            raise VarNotFoundError(signal.id)

    def eval(self, signal: Signal) -> bool | F:
        try:
            if signal.logical:
                return self.lvar_map[signal.id]
            else:
                return self.var_map[signal.id]
        except KeyError:
            raise VarNotFoundError(signal.id)


@dataclass
class Common:
    # All signals
    signals: List[Signal] = field(default_factory=list)
    # All asserts
    asserts: List[Assert] = field(default_factory=list)
    # Witness assignments
    vars: Vars = field(default_factory=Vars)


@dataclass
class Component:
    """Circuit Component"""

    name: str
    fullname: str
    com: Common = field(default_factory=Common)
    signals: List[Signal] = field(default_factory=list)
    signal_names: Dict[str, int] = field(default_factory=dict)
    assert_ids: List[int] = field(default_factory=list)
    parent: Optional[Component] = None
    children: List[Component] = field(default_factory=list)
    children_names: Dict[str, int] = field(default_factory=dict)
    inputs: List[InputOutput] = field(default_factory=list)
    outputs: List[InputOutput] = field(default_factory=list)
    state: ComponentState = ComponentState.STARTED
    parent_inputs: List[InputOutput] = field(default_factory=list)
    assignments: List[Assignment] = field(default_factory=list)

    @classmethod
    def main(cls):
        return cls("main", "main")

    def _io_iter(self, ss: List[InputOutput]) -> Iterator[Signal]:
        for input in ss:
            for signal in io_list(input):
                yield signal

    def input_signals_iter(self) -> Iterator[Signal]:
        return self._io_iter(self.inputs)

    def output_signals_iter(self) -> Iterator[Signal]:
        return self._io_iter(self.outputs)

    def parent_inputs_signal_iter(self) -> Iterator[Signal]:
        return self._io_iter(self.parent_inputs)

    def asserts_iter(self, all: bool = False) -> Iterator[Assert]:
        if all:
            for a in self.com.asserts:
                yield a
        else:
            for assert_id in self.assert_ids:
                yield self.com.asserts[assert_id]

    def unique_name(self, name: str, names: Dict[str, int]) -> str:
        sufix = ""
        if name in names:
            sufix = f"_{names[name]}"
            names[name] += 1
        else:
            names[name] = 1
        return f"{name}{sufix}"

    def unique_signal_name(self, name: str) -> str:
        return self.unique_name(name, self.signal_names)

    def Sub(self, name: str) -> Component:
        assert self.state == ComponentState.STARTED
        name = self.unique_name(name, self.children_names)
        sub_component = Component(name, f"{self.fullname}.{name}", com=self.com, parent=self)
        self.children.append(sub_component)
        return sub_component

    def Signal(self, type: Optional[Type] = None, name: Optional[str] = None, io: Optional[IO] = None) -> AVar:
        assert self.state == ComponentState.STARTED
        if name is None:
            name = varname(strict=False)
        name = self.unique_signal_name(name)
        id = len(self.com.signals)
        signal = Signal(name, f"{self.fullname}.{name}", id, inspect.stack()[1], type=type)
        self.com.signals.append(signal)
        self.signals.append(signal)
        return AVar(signal, self)

    def LSignal(self, name: Optional[str] = None) -> LVar:
        assert self.state == ComponentState.STARTED
        if name is None:
            name = varname(strict=False)
        name = self.unique_signal_name(name)
        id = len(self.com.signals)
        signal = Signal(name, f"{self.fullname}.{name}", id, inspect.stack()[1], logical=True)
        self.com.signals.append(signal)
        self.signals.append(signal)
        return LVar(signal, self)

    def In(self, signals: InputOutput) -> Any:
        self.inputs.append(signals)
        return signals

    def Out(self, signals: InputOutput) -> Any:
        self.outputs.append(signals)
        return signals

    def _push_assert(self, a: Assert):
        id = len(self.com.asserts)
        a.id = id
        self.com.asserts.append(a)
        self.assert_ids.append(id)

    def Eq(self, signal: AVar | LVar, e: AExpr | LExpr) -> Any:
        assert self.state == ComponentState.STARTED
        if isinstance(signal, AVar):
            assert isinstance(e, AExpr)
            a = Assert(signal == e, frame=inspect.stack()[1])
        elif isinstance(signal, LVar):
            assert isinstance(e, LExpr)
            a = Assert(signal == e, frame=inspect.stack()[1])
        self._push_assert(a)
        self.assignments.append(Assignment(AssignmentEq(a.id)))
        return signal

    def Range(self, signal: AVar, bound: StaticBound) -> Assert:
        assert self.state == ComponentState.STARTED
        bound = deepcopy(bound)
        r = RangeCheck(signal, bound)
        a = Assert(r, frame=inspect.stack()[1])
        self._push_assert(a)
        return a

    def Assert(self, s: Cond | LExpr) -> Assert:
        assert self.state == ComponentState.STARTED
        a = Assert(s, frame=inspect.stack()[1])
        self._push_assert(a)
        return a

    def If(self, cond: LExpr, true_e: Cond | LExpr) -> Cond:
        assert self.state == ComponentState.STARTED
        return Cond(If(cond, Assert(true_e)))

    def IfElse(self, cond: LExpr, true_e: Cond | LExpr, false_e: Cond | LExpr) -> Cond:
        assert self.state == ComponentState.STARTED
        return Cond(IfElse(cond, Assert(true_e), Assert(false_e)))

    def Finalize(self) -> Component:
        assert self.state == ComponentState.STARTED
        self.state = ComponentState.FINALIZED
        return self

    def Connect(self, inputs: List[InputOutput]) -> List[Any]:
        assert self.state == ComponentState.FINALIZED
        self.state = ComponentState.CONNECTED
        assert len(inputs) == len(self.inputs)
        for (i, parent_input) in enumerate(inputs):
            assert isinstance(parent_input, type(self.inputs[i]))
        self.parent_inputs = inputs
        assert self.parent is not None
        self.parent.assignments.append(Assignment(AssignmentComponent(self)))
        return self.outputs

    def Assign(self, var: AVar, fn: Callable[[], F | int]):
        self.assignments.append(Assignment(AssignmentManual(var.signal().id, fn)))

    def _witness_calc(self):
        assert self.state == ComponentState.CONNECTED
        self.state = ComponentState.WITNESS_ASSIGNED
        # print(f"DBG {self.assignments}")
        for assignment in self.assignments:
            match assignment.a:
                case AssignmentEq(assert_id):
                    a = self.com.asserts[assert_id]
                    lhs: Any = None
                    rhs: Any = None
                    match a.s:
                        case LExpr(Eq(AExprPair(_lhs, _rhs))):
                            (lhs, rhs) = (_lhs, _rhs)
                        case LExpr(Eq(LExprPair(_lhs, _rhs))):
                            (lhs, rhs) = (_lhs, _rhs)
                        case _:
                            raise ValueError
                    signal = lhs.as_var()
                    if signal is not None:
                        try:
                            rhs_eval = rhs.eval(self.com.vars)
                        except VarNotFoundError as e:
                            print(f"VarNotFound {self.com.signals[e.v].fullname} in \"{rhs}\"")
                            if a.frame is not None:
                                if a.frame.code_context is not None:
                                    code = '\n'.join(a.frame.code_context)
                                    print(f"> {a.frame.filename}:{a.frame.lineno}\n{code}")
                            raise e
                        self.com.vars.set(signal, rhs_eval)
                    else:
                        raise ValueError
                case AssignmentComponent(component):
                    for (signal_parent, signal_child) in zip(component.parent_inputs_signal_iter(), component.input_signals_iter()):
                        try:
                            signal_value = self.com.vars.eval(signal_child)
                        except VarNotFoundError as e:
                            print(f"VarNotFound {self.com.signals[e.v].fullname} in connect to {component.fullname}")
                            # TODO: Save frame in Connect and print it here
                            raise e
                        self.com.vars.set(signal_child, signal_value)
                    component._witness_calc()
                case AssignmentManual(signal_id, fn):
                    try:
                        signal_value = fn()
                        if isinstance(signal_value, int):
                            signal_value = F(signal_value)
                    except VarNotFoundError as e:
                        print(f"VarNotFound {self.com.signals[e.v].fullname} in Assign")
                        # TODO: Save frame in Assign and print it here
                        raise e
                    self.com.vars.set(self.com.signals[signal_id], signal_value)


    def WitnessCalc(self, inputs: List[bool | int | F]) -> Vars:
        self.com.vars = Vars()
        for (i, signal) in enumerate(self.input_signals_iter()):
            self.com.vars.set(signal, inputs[i])
        self._witness_calc()

        return self.com.vars

    def walk(self, fn: Callable[[Component], None]):
        fn(self)
        for child in self.children:
            child.walk(fn)

    def Verify(self):
        assert self.state == ComponentState.WITNESS_ASSIGNED
        for a in self.asserts_iter():
            try:
                if not a.verify(self.com.vars):
                    print(f"AssertNotSatisfied {a.s}")
                    if a.frame is not None:
                        if a.frame.code_context is not None:
                            code = '\n'.join(a.frame.code_context)
                            print(f"> {a.frame.filename}:{a.frame.lineno}\n{code}")
                    for signal in a.vars():
                        print(f" - {signal.fullname} = {self.com.vars.eval(signal)}")
            except VarNotFoundError as e:
                print(f"VarNotFound {self.com.signals[e.v].fullname} in")
                if a.frame is not None:
                    if a.frame.code_context is not None:
                        code = '\n'.join(a.frame.code_context)
                        print(f"> {a.frame.filename}:{a.frame.lineno}\n{code}")
                raise e
        for sub in self.children:
            sub.Verify()


    def type_check(self):
        print("Type check")
        # Assume input types are satisfied
        print("# Inputs")
        for signal in self.input_signals_iter():
            if signal.type is not None:
                signal.inferred, _ = signal.inferred.overlap(signal.type.t)
                print(f"- Assume {signal.fullname} is {signal.inferred}")

        # Assume outputs of sub-components types are satisied
        print("# SubComponents Outputs")
        for sub in self.children:
            for signal in sub.output_signals_iter():
                if signal.type is not None:
                    signal.inferred, _ = signal.inferred.overlap(signal.type.t)
                    print(f"- Assume {signal.fullname} is {signal.inferred}")

        # Infer from range checks
        print("# RangeChecks")
        for a in self.com.asserts:
            match a.s:
                case RangeCheck(var, bound):
                    signal = var.signal()
                    signal.inferred, _ = signal.inferred.overlap(bound)
                    print(f"- Range {signal.fullname} is {signal.inferred}")
                case _:
                    continue

        # Propagate
        print("# Inferred")
        while True:
            updates = 0
            for a in self.com.asserts:
                (lhs, rhs) = (None, None)
                match a.s:
                    case LExpr(Eq(AExprPair(_lhs, _rhs))):
                        (lhs, rhs) = (_lhs, _rhs)
                    case _:
                        continue
                rhs_bound = rhs.type_eval()
                signal = lhs.as_var()
                if signal is not None:
                    signal.inferred, update = signal.inferred.overlap(rhs_bound)
                    if signal.fullname == "main.mulAddWord.d_hi":
                        print(f" - DBG {rhs_bound} -> {signal.inferred}")
                    if update:
                        updates += 1
                        print(f"- Range {signal.fullname} is {signal.inferred}")
            if updates == 0:
                break

        print("# Overflows")
        # for a in self.com.asserts:
        #     (lhs, rhs) = (None, None)
        #     match a.s:
        #         case LExpr(Eq(AExprPair(_lhs, _rhs))):
        #             (lhs, rhs) = (_lhs, _rhs)
        #         case _:
        #             continue
        #     rhs_bound = rhs.type_eval()
        #     rhs_str = f"{rhs}".replace(f"{self.fullname}.", "")
        #     lhs_bound = lhs.type_eval()
        #     lhs_str = f"{lhs}".replace(f"{self.fullname}.", "")
        #     overlap, _ = rhs_bound.overlap(lhs_bound)
        #     if overlap.overflow():
        #         print(f" - Overflow {rhs_str} == {lhs_str}")
        for signal in self.signals:
            # print(f" - Signal {signal.fullname} {signal.inferred}")
            if signal.inferred.overflow():
                print(f" - Overflow of {signal.fullname}")

        print("# Type checks")
        for signal in self.signals:
            type = signal.type
            if type is None:
                continue
            if not signal.inferred.type_check(type.t):
                print(f" - Signal {signal.fullname} type '{type.name}':{type.t} not satisfied by {signal.inferred}")


def dump(x: Component):
    def _dump(x: Component):
        print(f"# {x.fullname}\n")
        for signal in x.signals:
            type = ""
            io = ""
            inputs = list(x.input_signals_iter())
            outputs = list(x.output_signals_iter())
            if signal.logical:
                type = " logical"
            elif signal.type is not None:
                type = f" {signal.type.name}"
            if signal.id in inputs:
                io = " in"
            elif signal.id in outputs:
                io = " out"
            print(f"signal{io}{type} {signal.fullname}")
        print()
        for a in x.asserts_iter():
            print(a)
        print()

    x.walk(_dump)


def graph(x: Component):
    def _print(i, str):
        print("  " * i + str)

    def name(signal: Signal) -> str:
        return signal.fullname.replace(".", "_")

    def _graph(x: Component, lvl: int):
        for (parent_signal, signal) in zip(x.parent_inputs_signal_iter(), x.input_signals_iter()):
            parent_fullname = name(parent_signal)
            fullname = name(signal)
            _print(lvl, f"{parent_fullname} -> {fullname};")
        fullname = x.fullname.replace(".", "_")
        _print(lvl, f"subgraph cluster_{fullname} {{")
        _print(lvl+1, f"label=\"{x.name}\";")

        inputs = list(x.input_signals_iter())
        outputs = list(x.output_signals_iter())
        assert_id = 0
        for signal in x.signals:
            prop = ""
            if signal.id in inputs:
                prop = ",color=green"
            elif signal.id in outputs:
                prop = ",color=orange"
            fullname = name(signal)
            _print(lvl+1, f"{fullname}[label=\"{signal.name}\"{prop}];")
        for a in x.asserts_iter():
            assert_name = f"assert_{fullname}{assert_id}"
            a_str = f"{a}"
            a_str = a_str.replace(f"{x.fullname}.", "")
            _print(lvl+1, f"{assert_name}[shape=rectangle,label=\"{a_str}\"];")
            assert_id += 1
            signal_refs = a.vars()
            for signal_ref in signal_refs:
                signal_name = name(x.com.signals[signal_ref.id])
                _print(lvl+1, f"{signal_name} -> {assert_name};")

        for child in x.children:
            _graph(child, lvl+1)
        _print(lvl, "}")

    print("")
    print("digraph G {")
    print("  rankdir = \"LR\";")
    _graph(x, 1)
    print("}")
