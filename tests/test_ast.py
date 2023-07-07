from zktypes.ast import AExpr, AVar, F, Cond, If, IfElse, Assert, StrVar, Component, LExpr, Type, LVar, io_list, graph, dump
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

    value = x.In(x.Signal())
    is_zero = x.Out(x.LSignal())

    value_inv = x.Signal()
    x.Eq(is_zero, ~(value * value_inv == 1))
    x.Assert((value == 0) | ~is_zero)

    return x.Finalize()


class Word:
    lo: AExpr
    hi: AExpr
    name: str

    def vars(self) -> List[AVar | LVar]:
        return [self.lo.as_var(), self.hi.as_var()]

    def __init__(self, x: Component, name: Optional[str] = None):
        if name is None:
            name = varname(strict=False)
        self.name = name
        self.lo = x.Signal(TypeU128, name=f"{name}_lo")
        self.hi = x.Signal(TypeU128, name=f"{name}_hi")

    def to_64bit_limbs(self, x: Component) -> List[AExpr]:
        l0 = x.Signal(TypeU64, name=f"{self.name}_0")
        l1 = x.Signal(TypeU64, name=f"{self.name}_1")
        l2 = x.Signal(TypeU64, name=f"{self.name}_2")
        l3 = x.Signal(TypeU64, name=f"{self.name}_3")
        for limb in [l0, l1, l2, l3]:
            x.Range(limb, TypeU64.t)
        x.Eq(self.lo, l0 + l1 * 2**64)
        x.Eq(self.hi, l2 + l3 * 2**64)
        return [l0, l1, l2, l3]


def WordTo64BitLimbs(x: Component, name: str) -> Component:
    # x = x.Sub("WordTo64BitLimbs")
    x = x.Sub(name)

    w = x.In(Word(x))
    l0 = x.Out(x.Signal(TypeU64))
    l1 = x.Out(x.Signal(TypeU64))
    l2 = x.Out(x.Signal(TypeU64))
    l3 = x.Out(x.Signal(TypeU64))
    for limb in [l0, l1, l2, l3]:
        x.Range(limb, TypeU64.t)
    x.Eq(w.lo, l0 + l1 * 2**64)
    x.Eq(w.hi, l2 + l3 * 2**64)

    return x.Finalize()


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
TypeU64 = Type.Bound(0, F(2**64-1))
TypeU128 = Type.Bound(0, F(2**128-1))
Type9B = Type.Bound(0, F(2**(9*8)-1))
TypeAny = Type.Any()


def test_component():
    x = Component.main()
    a = x.Signal()
    b = x.Signal()
    x.Assert(x.If(a == 13, b != 5))
    [isZero,] = IsZero(x).Connect([a])
    x.Assert(isZero)
    [isZero,] = IsZero(x).Connect([b])
    x.Assert(isZero)

    x.Assert(a == 0)
    x.Assert(x.If(a == 0, b == 42))

    word_a = Word(x)
    x.Range(word_a.lo, TypeU128.t)
    x.Range(word_a.hi, TypeU128.t)
    word_b = Word(x)
    x.Range(word_b.lo, TypeU128.t)
    x.Range(word_b.hi, TypeU128.t)
    [res, _] = Add256(x).Connect([word_a, word_b])
    x.Assert((res.lo == 1) & (res.hi == 1))

    graph(x)


def MulAddWord(x: Component) -> Component:
    """d = a * b + c"""
    x = x.Sub("mulAddWord")

    a = x.In(Word(x))
    b = x.In(Word(x))
    c = x.In(Word(x))
    d = x.Out(Word(x))
    x.Range(d.lo, TypeU128.t)
    x.Range(d.hi, TypeU128.t)
    has_overflow = x.Out(x.LSignal())

    # a64s = a.to_64bit_limbs(x)
    # b64s = b.to_64bit_limbs(x)
    a64s = WordTo64BitLimbs(x, "a").Connect([a])
    b64s = WordTo64BitLimbs(x, "b").Connect([b])

    TypeU132 = Type.Bound(0, F(2**123-1))
    t0 = x.Eq(x.Signal(TypeU132), a64s[0] * b64s[0])
    t1 = x.Eq(x.Signal(TypeU132), a64s[0] * b64s[1] + a64s[1] * b64s[0])
    t2 = x.Eq(x.Signal(TypeU132), a64s[0] * b64s[2] + a64s[1] * b64s[1] + a64s[2] * b64s[0])
    t3 = x.Eq(x.Signal(TypeU132), a64s[0] * b64s[3] + a64s[1] * b64s[2] + a64s[2] * b64s[1] + a64s[3] * b64s[0])

    carry_lo = x.Signal(Type9B)
    carry_hi = x.Signal(Type9B)
    # range check for carries
    x.Range(carry_lo, Type9B.t)
    x.Range(carry_hi, Type9B.t)
    x.Eq(d.lo, t0 + t1 * 2**64 + c.lo - carry_lo * 2**128)
    x.Eq(d.hi, carry_lo + t2 + t3 * 2**64 + c.hi - carry_hi * 2**128)
    # x.Assert(d.lo + carry_lo * 2**128 == t0 + t1 * 2**64 + c.lo)
    # x.Assert(d.hi + carry_hi * 2**128 == carry_lo + t2 + t3 * 2**64 + c.hi)

    overflow = x.Eq(
            x.Signal(),
            carry_hi
            + a64s[1] * b64s[3]
            + a64s[2] * b64s[2]
            + a64s[3] * b64s[1]
            + a64s[2] * b64s[3]
            + a64s[3] * b64s[2]
            + a64s[3] * b64s[3]
    )
    x.Eq(has_overflow, overflow != 0)

    # x.Assert(t0 + t1 * (2**64) + c.lo == d.lo + carry_lo * (2**128))
    # x.Assert(t2 + t3 * (2**64) + c.hi + carry_lo == d.hi + carry_hi * (2**128))

    return x.Finalize()


def MulModWord(x: Component) -> Component:
    """r = (a * b) mod n"""
    x = x.Sub("mulModWord")

    return x.Finalize()


def test_muladd():

    x = Component.main()

    a = Word(x)
    x.Range(a.lo, TypeU128.t)
    x.Range(a.hi, TypeU128.t)
    b = Word(x)
    x.Range(b.lo, TypeU128.t)
    x.Range(b.hi, TypeU128.t)
    c = Word(x)
    x.Range(c.lo, TypeU128.t)
    x.Range(c.hi, TypeU128.t)

    mul_add_words = MulAddWord(x)
    mul_add_words.type_check()
    [d, carry] = mul_add_words.Connect([a, b, c])

    # dump(x)
