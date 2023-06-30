from zktypes.ast import AExpr, AVar, F, Cond, If, IfElse, Assert, StrVar, Component, LExpr, Type, LVar, io_list
from varname import varname  # type: ignore
from typing import  Optional, Tuple, List


def var(s: str) -> AExpr:
    return AExpr(AVar(StrVar(s)))


def lvar(s: str) -> LExpr:
    return LExpr(LVar(StrVar(s)))


def test_aexpr_build():
    print(10 + var("a"))
    print(var("a") + 10)
    print(var("a") + 2 + 10)
    e = var("a") + 10
    print(e + var("b"))
    print(2 * e)
    print(e * 3)
    print(e - 3)
    print((var("a") + var("b")) * (2 - var("c")))


def test_lexpr_build():
    e1 = var("a") == var("b")
    e2 = var("a") != var("b")
    print(e1)
    print(e2)
    print(e1 == e2)
    print(~e1)
    print(e1 & e2)
    print(e1 | e2)
    e3 = var("c") == 42

    a1 = Cond(If(e1 & e2, Assert(e3)))
    print(Cond(If(e1 | e2, Assert(a1))))
    c = Cond(IfElse(e1 | e2, Assert(a1), Assert(var("c") == 13)))
    print(c)


def test_aexpr_eval():
    va = 2
    vb = 3
    vs = {"a": F(va), "b": F(vb)}

    def var_eval(v: StrVar) -> F:
        return vs[v.s]

    e1 = (10 + var("a") * var("b") - 5) * (var("a") ** 2)
    assert e1.eval(var_eval) == F((10 + va * vb - 5) * (va ** 2))

    e2 = var("a") - var("b")
    assert e2.eval(var_eval) == F(-1)


def test_verify():
    vs = {"a": F(2), "b": F(3)}

    def var_eval(v: StrVar) -> F:
        return vs[v.s]

    assert Cond(If(var("a") == 2,
                   Assert(var("b") == 3))).verify(var_eval) == True
    assert Cond(If(var("a") == 2,
                   Assert(var("b") == 4))).verify(var_eval) == False
    assert Cond(If(var("a") != 2,
                   Assert(var("b") == 4))).verify(var_eval) == True

    assert Cond(IfElse(var("a") != 2,
                   Assert(var("b") == 4),
                   Assert(var("b") == 3))).verify(var_eval) == True
    assert Cond(IfElse(var("a") != 2,
                   Assert(var("b") == 4),
                   Assert(var("b") != 3))).verify(var_eval) == False

    assert Assert((var("a") == 2) & (var("b") == 3)).verify(var_eval) == True
    assert Assert((var("a") == 5) | (var("b") == 3)).verify(var_eval) == True
    assert Assert(~(var("a") == 5)).verify(var_eval) == True


def IsZero(x: Component) -> Component:
    x = x.Sub("isZero")

    value = x.In(x.Signal(TypeAny))
    is_zero = x.Out(x.LSignal())

    value_inv = x.Signal()
    x.Eq(is_zero, ~(value * value_inv == 1))
    x.Assert((value == 0) | ~is_zero)

    return x.Finalize()


class Word:
    lo: AExpr
    hi: AExpr

    def vars(self) -> List[AExpr | LExpr]:
        return [self.lo, self.hi]

    def __init__(self, x: Component, name: Optional[str] = None):
        if not name:
            name = varname(strict=False)
        self.lo = x.Signal(name=f"{name}.lo")
        self.hi = x.Signal(name=f"{name}.hi")


def Add256(x: Component) -> Component:
    x = x.Sub("add256")

    a = x.In(Word(x))
    b = x.In(Word(x))
    res = x.Out(Word(x))
    carry_hi = x.Out(x.Signal(TypeU1))
    carry_lo = x.Signal(TypeU1)

    x.Assert(a.lo + b.lo == res.lo + carry_lo * 2**128)
    x.Assert(a.hi + b.hi + carry_lo == res.hi + carry_hi * 2**128)

    return x.Finalize()


TypeU1 = Type.Bound(0, 1)
TypeU8 = Type.Bound(0, 255)
TypeU128 = Type.Bound(0, F(2**128))
TypeAny = Type.Any()


def test_component():
    x = Component.main()
    a = x.Signal()
    b = x.Signal()
    x.Assert(x.If(a == 13, b != 5))
    [isZero,] = IsZero(x).Connect([a])
    x.Assert(isZero)

    x.Assert(a == 0)
    x.Assert(x.If(a == 0, b == 42))

    word_a = Word(x)
    word_b = Word(x)
    [res, _] = Add256(x).Connect([word_a, word_b])
    x.Assert((res.lo == 1) & (res.hi == 1))

    # ---
    def dump(x: Component):
        print(f"# {x.fullname}\n")
        for id in x.signal_ids:
            signal = x.signals[id]
            type = ""
            io = ""
            inputs = x.inputs_signal_ids()
            outputs = x.outputs_signal_ids()
            if signal.logical:
                type = " logical"
            if id in inputs:
                io = " in"
            elif id in outputs:
                io = " out"
            print(f"signal{io}{type} {x.signals[id].fullname}")
        print()
        for a in x.asserts:
            print(a)
        print()

    x.walk(dump)
