from zktypes.ast import AExpr, Var, F, Cond, If, IfElse, Assert, StrVar, Component, LExpr, Type
from varname import varname  # type: ignore
from typing import  Optional, Tuple


def var(s: str) -> AExpr:
    return AExpr(Var(StrVar(s)))


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


TypeU8 = Type.Bound(0, 255)
TypeU128 = Type.Bound(0, F(2**128))


def test_component():
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
