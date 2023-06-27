# Needed to annotate with a type that hasn't been defined yet.
from __future__ import annotations

from functools import reduce
from varname import varname  # type: ignore
from dataclasses import dataclass, field
from py_ecc import bn128
from typing import List, Union, Optional, Callable, Any, Self, TypeVar, Generic, Tuple
from typing_extensions import Protocol
import inspect

F = bn128.FQ


class SupportsFmtAscii(Protocol):
    def fmt_ascii(self) -> str:
        ...


V = TypeVar("V", bound=SupportsFmtAscii)


@dataclass
class StrVar:
    s: str

    def __hash__(self):
        return self.s.__hash__()

    def fmt_ascii(self) -> str:
        return self.s


@dataclass
class Var(Generic[V]):
    v: V

    def fmt_ascii(self) -> str:
        return self.v.fmt_ascii()


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
                return e
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

    def __pow__(a: ToAExpr, b: int) -> AExpr:
        a = to_aexpr(a)
        return AExpr(Pow(a, b))

    def __req__(b: ToAExpr, a: ToAExpr) -> LExpr:
        return AExpr.__eq__(a, b)

    def __eq__(a: ToAExpr, b: ToAExpr) -> LExpr:  # type: ignore
        (a, b) = (to_aexpr(a), to_aexpr(b))
        return LExpr(Eq(AExprPair(a, b)))

    def __rne__(b: ToAExpr, a: ToAExpr) -> LExpr:
        return AExpr.__ne__(a, b)

    def __ne__(a: ToAExpr, b: ToAExpr) -> LExpr:  # type: ignore
        (a, b) = (to_aexpr(a), to_aexpr(b))
        return LExpr(Neq(AExprPair(a, b)))

    def eval(self, var_eval: Callable[[Any], F]) -> F:
        match self.e:
            case Neg(e):
                return -e.eval(var_eval)
            case Pow(e, p):
                return e.eval(var_eval) ** p
            case Const(c):
                return c
            case Var(v):
                return var_eval(v)
            case Sum(es):
                return sum([e.eval(var_eval) for e in es], start=F(0))
            case Mul(es):
                return reduce(lambda x, y: x * y, [e.eval(var_eval) for e in es], F(1))

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
                c_bin = bin(c.n)[2:]
                if len(c_bin) >= 8 and c_bin.count("1") == 1:
                    return f"2^{len(c_bin)-1}"
                elif len(c_bin) >= 16:
                    return f"0x{c.n:02x}"
                else:
                    return f"{c}"
            case Var(_) as e:
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


ToAExpr = AExpr | str | int | F


@dataclass
class AExprPair:
    lhs: AExpr
    rhs: AExpr


@dataclass
class LExprPair:
    lhs: LExpr
    rhs: LExpr


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

    e: And | Or | Not | Eq | Neq

    def __eq__(a: LExpr, b: LExpr) -> LExpr:  # type: ignore
        """called with `==`"""
        return LExpr(Eq(LExprPair(a, b)))

    def __ne__(a: LExpr, b: LExpr) -> LExpr:  # type: ignore
        """called with `!=`"""
        return LExpr(Neq(LExprPair(a, b)))

    def __invert__(self: LExpr) -> LExpr:
        """not.  Called with `~`"""
        return LExpr(Not(self))

    def __and__(a: LExpr, b: LExpr) -> LExpr:
        """Called with `&`"""
        match (a.e, b.e):
            case (And(es), _):
                es = es + [b]
                return LExpr(And(es))
            case (_, And(es)):
                es = es + [b]
                return LExpr(And(es))
            case _:
                return LExpr(And([a, b]))

    def __or__(a: LExpr, b: LExpr) -> LExpr:
        """Called with `|`"""
        match (a.e, b.e):
            case (Or(es), _):
                es = es + [b]
                return LExpr(Or(es))
            case (_, Or(es)):
                es = es + [b]
                return LExpr(Or(es))
            case _:
                return LExpr(Or([a, b]))

    def eval(self, var_eval: Callable[[Any], F]) -> bool:
        match self.e:
            case And(es):
                return reduce(lambda x, y: x and y, [e.eval(var_eval) for e in es], True)
            case Or(es):
                return reduce(lambda x, y: x or y, [e.eval(var_eval) for e in es], False)
            case Not(e):
                return not e.eval(var_eval)
            case Eq(pair):
                match pair:
                    case AExprPair(lhs, rhs):
                        return lhs.eval(var_eval) == rhs.eval(var_eval)
                    case LExprPair(lhs, rhs):
                        return lhs.eval(var_eval) == rhs.eval(var_eval)
            case Neq(pair):
                match pair:
                    case AExprPair(lhs, rhs):
                        return lhs.eval(var_eval) != rhs.eval(var_eval)
                    case LExprPair(lhs, rhs):
                        return lhs.eval(var_eval) != rhs.eval(var_eval)

    def is_terminal(self: LExpr) -> bool:
        match self.e:
            case Not(_):
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


@dataclass
class Assert:
    s: Cond | LExpr
    frame: Optional[inspect.FrameInfo] = None

    def __str__(self: Assert) -> str:
        return self.s.__str__()

    def verify(self, var_eval: Callable[[Any], F]) -> bool:
        match self.s:
            case Cond(_) as a:
                return a.verify(var_eval)
            case LExpr(_) as e:
                return e.eval(var_eval)


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

    def verify(self, var_eval: Callable[[Any], F]) -> bool:
        match self.c:
            case If(cond, true_e):
                if cond.eval(var_eval):
                    return true_e.verify(var_eval)
                else:
                    True
            case IfElse(cond, true_e, false_e):
                if cond.eval(var_eval):
                    return true_e.verify(var_eval)
                else:
                    return false_e.verify(var_eval)
            case Switch(_, _):
                raise NotImplementedError
        return False # TODO: This should be unreachable


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
        raise ValueError(f"type `{type(v)}` is not ToAExpr")


@dataclass
class Signal:
    name: str
    fullname: str
    frame: inspect.FrameInfo

    def fmt_ascii(self) -> str:
        return self.name


@dataclass
class SignalId:
    id: int
    signals: List[Signal]

    def fmt_ascii(self) -> str:
        return self.signals[self.id].fullname


class Component:
    """Circuit Component"""

    name: str
    fullname: str
    signals: List[Signal]
    signal_ids: List[int]
    asserts: List[Assert]
    children: List[Component]

    def __init__(self, name: str, fullname: str, signals: List[Signal]):
        self.name = name
        self.fullname = fullname
        self.signals = signals
        self.signal_ids = []
        self.asserts = []
        self.children = []

    @classmethod
    def main(cls):
        return cls("main", "main", [])

    def sub(self, name: str) -> Component:
        sub_component = Component(name, f"{self.fullname}.{name}", self.signals)
        self.children.append(sub_component)
        return sub_component

    def Signal(self, name: Optional[str] = None) -> AExpr:
        if name is None:
            name = varname()
        signal = Signal(name, f"{self.fullname}.{name}", inspect.stack()[1])
        self.signals.append(signal)
        id = len(self.signals) - 1
        self.signal_ids.append(id)
        return AExpr(Var(SignalId(id, self.signals)))

    def Assert(self, s: Cond | LExpr) -> Assert:
        a = Assert(s, inspect.stack()[1])
        self.asserts.append(a)
        return a

    def If(self, cond: LExpr, true_e: Cond | LExpr) -> Cond:
        return Cond(If(cond, Assert(true_e)))

    def IfElse(self, cond: LExpr, true_e: Cond | LExpr, false_e: Cond | LExpr) -> Cond:
        return Cond(IfElse(cond, Assert(true_e), Assert(false_e)))

    def walk(self, fn: Callable[[Component], None]):
        fn(self)
        for child in self.children:
            child.walk(fn)


def IsZero(x: Component, value: AExpr) -> LExpr:
    x = x.sub("isZero")
    value_inv = x.Signal()
    is_zero = ~(value * value_inv == 1)
    x.Assert((value == 0) | ~is_zero)
    return is_zero


class Word:
    lo: AExpr
    hi: AExpr

    def __init__(self, x: Component, name: Optional[str] = None):
        if not name:
            name = varname()
        self.lo = x.Signal(f"{name}.lo")
        self.hi = x.Signal(f"{name}.hi")


def Add256(x: Component, a: Word, b: Word) -> Tuple[Word, AExpr]:
    x = x.sub("add256")
    res = Word(x)
    carry_lo = x.Signal()
    carry_hi = x.Signal()
    x.Assert(a.lo + b.lo == res.lo + carry_lo * 2**128)
    x.Assert(a.hi + b.hi + carry_lo == res.hi + carry_hi * 2**128)
    return (res, carry_hi)


def main():
    x = Component.main()
    a = x.Signal()
    b = x.Signal()
    x.Assert(x.If(a == 13, b != 5))
    isZero = IsZero(x, a)
    x.Assert(isZero)

    x.Assert(a == 0)
    x.Assert(x.If(a == 0, b == 42))

    word_a = Word(x)
    word_b = Word(x)
    (res, _) = Add256(x, word_a, word_b)
    x.Assert((res.lo == 1) & (res.hi == 1))

    # ---
    def dump(x: Component):
        print(f"# {x.fullname}\n")
        for id in x.signal_ids:
            print(f"signal {x.signals[id].fullname}")
        print()
        for a in x.asserts:
            print(a)
        print()

    x.walk(dump)


if __name__ == "__main__":
    main()
