# Needed to annotate with a type that hasn't been defined yet.
from __future__ import annotations

from functools import reduce
from itertools import chain
from enum import Enum, auto
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


class SupportsVars(Protocol):
    def vars(self) -> List[AExpr | LExpr]:
        ...


class SupportsEval(Protocol):
    def var_eval(self, Any) -> F:
        ...

    def lvar_eval(self, Any) -> bool:
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
    typ: Optional[Type] = None

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

    def type(self, type: Type) -> AExpr:
        self.typ = type
        return self

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
                c_bin = bin(c.n)[2:]
                if len(c_bin) >= 8 and c_bin.count("1") == 1:
                    return f"2^{len(c_bin)-1}"
                elif len(c_bin) >= 16:
                    return f"0x{c.n:02x}"
                else:
                    return f"{c}"
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
class Assert:
    s: Cond | LExpr
    frame: Optional[inspect.FrameInfo] = None

    def __str__(self: Assert) -> str:
        return self.s.__str__()

    def verify(self, vars: SupportsEval) -> bool:
        match self.s:
            case Cond(_) as a:
                return a.verify(vars)
            case LExpr(_) as e:
                return e.eval(vars)


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
    interval: Tuple[F, F]

    def __init__(self, start: int | F, end: int | F):
        if isinstance(start, int):
            start = F(start)
        if isinstance(end, int):
            end = F(end)
        self.interval = (start, end)


@dataclass
class Type:
    name: str
    t: StaticBound
    inferred: bool = False
    force: bool = False

    @classmethod
    def Bound(cls, start: int | F, end: int | F, name: Optional[str] = None):
        if name is None:
            name = varname()
        return cls(name, StaticBound(start, end))

    @classmethod
    def Any(cls):
        return cls("Any", StaticBound(F(0), F(-1)))

    def forced(self) -> Type:
        return Type(self.name, self.t, force=True)


@dataclass
class Signal:
    name: str
    fullname: str
    frame: inspect.FrameInfo
    logical: bool = False

    def fmt_ascii(self) -> str:
        return self.name


@dataclass
class SignalId:
    id: int
    signals: List[Signal]

    def fmt_ascii(self) -> str:
        return self.signals[self.id].fullname


InputOutput = AExpr | LExpr | List[AExpr | LExpr] | SupportsVars


def io_list(io: InputOutput) -> List[AVar | LVar]:
    result: List[AExpr | LExpr] = []
    match io:
        case AExpr(_) as v:
            result = [v]
        case LExpr(_) as v:
            result = [v]
        case [*_] as vs:
            result = vs
        case _:
            result = io.vars()
    for v in result:
        assert v.is_var()
    return [v.as_var() for v in result]


class IO(Enum):
    IN = auto()
    OUT = auto()


class ComponentState(Enum):
    STARTED = auto()
    FINALIZED = auto()
    CONNECTED = auto()


class Component:
    """Circuit Component"""

    name: str
    fullname: str
    signals: List[Signal]
    signal_ids: List[int]
    asserts: List[Assert]
    children: List[Component]
    inputs: List[InputOutput]
    outputs: List[InputOutput]
    state: ComponentState
    parent_inputs: List[InputOutput]

    def __init__(self, name: str, fullname: str, signals: List[Signal]):
        self.name = name
        self.fullname = fullname
        self.signals = signals
        self.signal_ids = []
        self.asserts = []
        self.children = []
        self.inputs = []
        self.outputs = []
        self.parent_inputs = []
        self.state = ComponentState.STARTED

    @classmethod
    def main(cls):
        return cls("main", "main", [])

    def inputs_signal_ids(self) -> List[int]:
        return [s1.id for s1 in list(chain(*[io_list(s) for s in self.inputs]))]

    def outputs_signal_ids(self) -> List[int]:
        return [s1.id for s1 in list(chain(*[io_list(s) for s in self.outputs]))]

    def Sub(self, name: str) -> Component:
        assert self.state == ComponentState.STARTED
        sub_component = Component(name, f"{self.fullname}.{name}", self.signals)
        self.children.append(sub_component)
        return sub_component

    def Signal(self, type: Optional[Type] = None, name: Optional[str] = None, io: Optional[IO] = None) -> AExpr:
        assert self.state == ComponentState.STARTED
        if name is None:
            name = varname(strict=False)
        signal = Signal(name, f"{self.fullname}.{name}", inspect.stack()[1])
        self.signals.append(signal)
        id = len(self.signals) - 1
        self.signal_ids.append(id)
        e = AExpr(AVar(SignalId(id, self.signals)))
        if type is not None:
            e.type(type)
        return e

    def LSignal(self, name: Optional[str] = None) -> LExpr:
        assert self.state == ComponentState.STARTED
        if name is None:
            name = varname(strict=False)
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

    def Eq(self, signal: AExpr | LExpr, e: AExpr | LExpr) -> Assert:
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
