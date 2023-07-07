# Needed to annotate with a type that hasn't been defined yet.
from __future__ import annotations

from copy import deepcopy
from functools import reduce
from itertools import chain
from enum import Enum, auto
from varname import varname  # type: ignore
from dataclasses import dataclass, field
from py_ecc import bn128
from typing import List, Union, Optional, Callable, Any, Self, TypeVar, Generic, Tuple, Dict
from typing_extensions import Protocol
import inspect

F = bn128.FQ


class SupportsFmtAscii(Protocol):
    def fmt_ascii(self) -> str:
        ...


class SupportsVars(Protocol):
    def vars(self) -> List[AVar | LVar]:
        ...


class SupportsEval(Protocol):
    def var_eval(self, Any) -> F:
        ...

    def lvar_eval(self, Any) -> bool:
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
class AVar(Generic[V]):
    """Arithmetic Variable"""
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

    e: Const | AVar | Sum | Mul | Neg | Pow

    def case_id(self: AExpr) -> int:
        match self.e:
            case Const(_):
                return 0
            case AVar(_):
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
            case AVar(_):
                return True
            case _:
                return False

    def as_var(self) -> Optional[Any]:
        match self.e:
            case AVar(v):
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
            case AVar(v):
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

    def __truediv__(a: ToAExpr, b: int) -> AExpr:
        a = to_aexpr(a)
        b_inv = F(1) / b
        return a * b_inv

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

    def type_eval(self) -> StaticBound:
        match self.e:
            case Neg(e):
                bound = e.type_eval()
                end = -bound.interval[0]
                start = -bound.interval[1]
                return StaticBound(start, end)
            case Pow(e, p):
                if p == 0:
                    return StaticBound(1, 1)
                bound = e.type_eval()
                for _ in range(1, p):
                    bound = bound * bound
                return bound
            case Const(c):
                return StaticBound(c, c)
            case AVar(v):
                return v.signals[v.id].inferred
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
            case AVar(v):
                return vars.var_eval(v)
            case Sum(es):
                return sum([e.eval(vars) for e in es], start=F(0))
            case Mul(es):
                return reduce(lambda x, y: x * y, [e.eval(vars) for e in es], F(1))

    def is_terminal(self: AExpr) -> bool:
        match self.e:
            case Const(_) | AVar(_) | Pow(_, _):
                return True
            case _:
                return False

    def is_mul_terminal(self: AExpr) -> bool:
        match self.e:
            case Const(_) | AVar(_) | Mul(_) | Pow(_, _):
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
                return f_fmt_ascii(c)
            case AVar(_) as e:
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
class LVar(Generic[V]):
    """Logical Variable"""
    v: V

    def fmt_ascii(self) -> str:
        return self.v.fmt_ascii()


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
            case LVar(_):
                return True
            case _:
                return False

    def as_var(self) -> Optional[Any]:
        match self.e:
            case LVar(v):
                return v
            case _:
                return None

    def vars(self) -> List[Any]:
        match self.e:
            case LVar(v):
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

    def eval(self, vars: SupportsEval) -> bool:
        match self.e:
            case LVar(v):
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
            case LVar(_) | Not(_):
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
            case LVar(_) as e:
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


@dataclass
class RangeCheck:
    e: AVar
    bound: StaticBound

    def __str__(self) -> str:
        return f"{self.e.fmt_ascii()} in {self.bound}"


@dataclass
class Assert:
    s: Cond | LExpr | RangeCheck
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
            case RangeCheck(_v, bound):
                v: F = vars.var_eval(_v)
                return bound.interval[0] <= v.n and v.n <= bound.interval[1]


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
    elif isinstance(v, F):
        return AExpr(Const(v))
    elif isinstance(v, int):
        if v >= 0:
            return AExpr(Const(F(v)))
        else:
            return AExpr(Neg(AExpr(Const(F(-v)))))
    else:
        raise ValueError(f"type `{type(v)}` is not ToAExpr")


class StaticBound:
    """Bound an expression between [interval[0], interval[1]]"""
    interval: Tuple[int, int]

    def __init__(self, start: int | F, end: int | F):
        if isinstance(start, F):
            start = start.n
        if isinstance(end, F):
            end = end.n
        assert start <= end
        self.interval = (start, end)

    @classmethod
    def default(cls) -> StaticBound:
        return StaticBound(F(0), F(-1))

    def overflow(self) -> bool:
        return self.interval[0] < 0 or self.interval[1] > F(-1).n

    def __add__(a: StaticBound, b: StaticBound) -> StaticBound:
        start = a.interval[0] + b.interval[0]
        end = a.interval[1] + b.interval[1]
        return StaticBound(start, end)

    def __mul__(a: StaticBound, b: StaticBound) -> StaticBound:
        start = a.interval[0] * b.interval[0]
        end = a.interval[1] * b.interval[1]
        return StaticBound(start, end)

    def overlap(self: StaticBound, other: StaticBound) -> bool:
        start = max(self.interval[0], other.interval[0])
        end = min(self.interval[1], other.interval[1])
        update = self.interval[0] != start or self.interval[1] != end
        self.interval = (start, end)
        return update

    def __str__(self) -> str:
        start = i_fmt_ascii(self.interval[0])
        end = i_fmt_ascii(self.interval[1])
        return f"[{start}, {end}]"


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
    frame: inspect.FrameInfo
    type: Optional[Type] = None
    inferred: StaticBound = StaticBoundDefault
    logical: bool = False

    def __post_init__(self):
        self.inferred = deepcopy(self.inferred)
        self.type = deepcopy(self.type)

    def fmt_ascii(self) -> str:
        return self.name


@dataclass
class SignalId:
    id: int
    signals: List[Signal]

    def fmt_ascii(self) -> str:
        return self.signals[self.id].fullname


InputOutput = AVar | LVar | List[AVar | LVar] | SupportsVars


def io_list(io: InputOutput) -> List[AVar | LVar]:
    result: List[AVar | LVar] = []
    match io:
        case AVar(_) as v:
            result = [v]
        case LVar(_) as v:
            result = [v]
        case [*_] as vs:
            result = vs
        case _:
            result = io.vars()
    return result


class IO(Enum):
    IN = auto()
    OUT = auto()


class ComponentState(Enum):
    STARTED = auto()
    FINALIZED = auto()
    CONNECTED = auto()


@dataclass
class Component:
    """Circuit Component"""

    name: str
    fullname: str
    signals: List[Signal] = field(default_factory=list)
    signal_ids: List[int] = field(default_factory=list)
    signal_names: Dict[str, int] = field(default_factory=dict)
    asserts: List[Assert] = field(default_factory=list)
    children: List[Component] = field(default_factory=list)
    children_names: Dict[str, int] = field(default_factory=dict)
    inputs: List[InputOutput] = field(default_factory=list)
    outputs: List[InputOutput] = field(default_factory=list)
    state: ComponentState = ComponentState.STARTED
    parent_inputs: List[InputOutput] = field(default_factory=list)

    @classmethod
    def main(cls):
        return cls("main", "main")

    def inputs_signal_ids(self) -> List[int]:
        return [s1.id for s1 in list(chain(*[io_list(s) for s in self.inputs]))]

    def outputs_signal_ids(self) -> List[int]:
        return [s1.id for s1 in list(chain(*[io_list(s) for s in self.outputs]))]

    def parent_inputs_signal_ids(self) -> List[int]:
        return [s1.id for s1 in list(chain(*[io_list(s) for s in self.parent_inputs]))]

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
        sub_component = Component(name, f"{self.fullname}.{name}", signals=self.signals)
        self.children.append(sub_component)
        return sub_component

    def Signal(self, type: Optional[Type] = None, name: Optional[str] = None, io: Optional[IO] = None) -> AExpr:
        assert self.state == ComponentState.STARTED
        if name is None:
            name = varname(strict=False)
        name = self.unique_signal_name(name)
        signal = Signal(name, f"{self.fullname}.{name}", inspect.stack()[1], type=type)
        self.signals.append(signal)
        id = len(self.signals) - 1
        self.signal_ids.append(id)
        e = AExpr(AVar(SignalId(id, self.signals)))
        return e

    def LSignal(self, name: Optional[str] = None) -> LExpr:
        assert self.state == ComponentState.STARTED
        if name is None:
            name = varname(strict=False)
        name = self.unique_signal_name(name)
        signal = Signal(name, f"{self.fullname}.{name}", inspect.stack()[1], logical=True)
        self.signals.append(signal)
        id = len(self.signals) - 1
        self.signal_ids.append(id)
        e = LExpr(LVar(SignalId(id, self.signals)))
        return e

    def In(self, signals: InputOutput) -> Any:
        self.inputs.append(signals)
        return signals

    def Out(self, signals: InputOutput) -> Any:
        self.outputs.append(signals)
        return signals

    def Eq(self, signal: AExpr | LExpr, e: AExpr | LExpr) -> AExpr | LExpr:
        assert self.state == ComponentState.STARTED
        if isinstance(signal, AExpr):
            assert signal.is_var(), f"`{signal}` is not a AVar"
            assert isinstance(e, AExpr)
            a = Assert(signal == e, inspect.stack()[1])
        elif isinstance(signal, LExpr):
            assert signal.is_var(), f"`{signal}` is not a LVar"
            assert isinstance(e, LExpr)
            a = Assert(signal == e, inspect.stack()[1])
        self.asserts.append(a)
        return signal

    def Range(self, e: AExpr, bound: StaticBound) -> Assert:
        assert self.state == ComponentState.STARTED
        assert e.is_var(), f"`{e}` is not a AVar"
        bound = deepcopy(bound)
        v = e.as_var()
        r = RangeCheck(v, bound)
        a = Assert(r, inspect.stack()[1])
        self.asserts.append(a)
        return a

    def Assert(self, s: Cond | LExpr) -> Assert:
        assert self.state == ComponentState.STARTED
        a = Assert(s, inspect.stack()[1])
        self.asserts.append(a)
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

    def Connect(self, inputs: List[InputOutput]) -> List[InputOutput]:
        assert self.state == ComponentState.FINALIZED
        assert len(inputs) == len(self.inputs)
        for (i, parent_input) in enumerate(inputs):
            assert isinstance(parent_input, type(self.inputs[i]))
        self.state = ComponentState.CONNECTED
        self.parent_inputs = inputs
        return self.outputs

    def walk(self, fn: Callable[[Component], None]):
        fn(self)
        for child in self.children:
            child.walk(fn)

    # def verify(self, inputs: List[int | F]):
    #     vars = {}
    #     for signal_
    #     input_signal_ids = signal.inputs_signal_ids()
    #     for child in self.children:
    #         child.walk(fn)
    #     fn(self)


    def type_check(self):
        print("Type check")
        # Assume input types are satisfied
        print("# Inputs")
        for id in self.inputs_signal_ids():
            signal = self.signals[id]
            if signal.type is not None:
                signal.inferred.overlap(signal.type.t)
                print(f"- Assume {signal.fullname} is {signal.inferred}")

        # Assume outputs of sub-components types are satisied
        print("# SubComponents Outputs")
        for sub in self.children:
            for id in sub.outputs_signal_ids():
                signal = self.signals[id]
                if signal.type is not None:
                    signal.inferred.overlap(signal.type.t)
                    print(f"- Assume {signal.fullname} is {signal.inferred}")

        # Infer from range checks
        print("# RangeChecks")
        for a in self.asserts:
            r = None
            match a.s:
                case RangeCheck(_, _) as check:
                    r = check
                case _:
                    continue
            signal = self.signals[r.e.id]
            signal.inferred.overlap(r.bound)
            print(f"- Range {signal.fullname} is {signal.inferred}")

        # Propagate
        print("# Inferred")
        while True:
            updates = 0
            for a in self.asserts:
                (lhs, rhs) = (None, None)
                match a.s:
                    case LExpr(Eq(AExprPair(_lhs, _rhs))):
                        (lhs, rhs) = (_lhs, _rhs)
                    case _:
                        continue
                rhs_bound = rhs.type_eval()
                if lhs.is_var():
                    signal_id = lhs.as_var()
                    signal = self.signals[signal_id.id]
                    if signal.inferred.overlap(rhs_bound):
                        updates += 1
                        print(f"- Range {signal.fullname} is {signal.inferred}")
            if updates == 0:
                break

        print("# Overflows")
        for a in self.asserts:
            (lhs, rhs) = (None, None)
            match a.s:
                case LExpr(Eq(AExprPair(_lhs, _rhs))):
                    (lhs, rhs) = (_lhs, _rhs)
                case _:
                    continue
            rhs_bound = rhs.type_eval()
            rhs_str = f"{rhs}".replace(f"{self.fullname}.", "")
            lhs_bound = lhs.type_eval()
            lhs_str = f"{lhs}".replace(f"{self.fullname}.", "")
            if rhs_bound.overflow():
                print(f" - Overflow {rhs_bound} in {rhs_str}")
            if lhs_bound.overflow():
                print(f" - Overflow {lhs_bound} in {lhs_str}")


def dump(x: Component):
    def _dump(x: Component):
        print(f"# {x.fullname}\n")
        for id in x.signal_ids:
            signal = x.signals[id]
            type = ""
            io = ""
            inputs = x.inputs_signal_ids()
            outputs = x.outputs_signal_ids()
            if signal.logical:
                type = " logical"
            elif signal.type is not None:
                type = f" {signal.type.name}"
            if id in inputs:
                io = " in"
            elif id in outputs:
                io = " out"
            print(f"signal{io}{type} {x.signals[id].fullname}")
        print()
        for a in x.asserts:
            print(a)
        print()

    x.walk(_dump)


def graph(x: Component):
    def _print(i, str):
        print("  " * i + str)

    def name(x: Component, signal_id: int) -> str:
        signal = x.signals[signal_id]
        return signal.fullname.replace(".", "_")

    def _graph(x: Component, lvl: int):
        for (parent_id, id) in zip(x.parent_inputs_signal_ids(), x.inputs_signal_ids()):
            parent_fullname = name(x, parent_id)
            fullname = name(x, id)
            _print(lvl, f"{parent_fullname} -> {fullname};")
        fullname = x.fullname.replace(".", "_")
        _print(lvl, f"subgraph cluster_{fullname} {{")
        _print(lvl+1, f"label=\"{x.name}\";")

        inputs = x.inputs_signal_ids()
        outputs = x.outputs_signal_ids()
        assert_id = 0
        for id in x.signal_ids:
            prop = ""
            if id in inputs:
                prop = ",color=green"
            elif id in outputs:
                prop = ",color=orange"
            fullname = name(x, id)
            _print(lvl+1, f"{fullname}[label=\"{x.signals[id].name}\"{prop}];")
        for a in x.asserts:
            assert_name = f"assert_{fullname}{assert_id}"
            a_str = f"{a}"
            a_str = a_str.replace(f"{x.fullname}.", "")
            _print(lvl+1, f"{assert_name}[shape=rectangle,label=\"{a_str}\"];")
            assert_id += 1
            vars = a.vars()
            for var in vars:
                var_name = name(x, var.id)
                _print(lvl+1, f"{var_name} -> {assert_name};")

        for child in x.children:
            _graph(child, lvl+1)
        _print(lvl, "}")

    print("")
    print("digraph G {")
    print("  rankdir = \"LR\";")
    _graph(x, 1)
    print("}")
