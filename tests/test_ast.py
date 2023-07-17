from zktypes.ast import (
    AVar,
    F,
    Cond,
    If,
    IfElse,
    Assert,
    Component,
    Type,
    LVar,
    graph,
    dump,
    Vars,
)
from varname import varname  # type: ignore
from typing import Optional, List

x = Component.main()


def var(s: str) -> AVar:
    return x.Signal(name=s)


def lvar(s: str) -> LVar:
    return x.LSignal(name=s)


def test_aexpr_build():
    global x
    x = Component.main()

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
    global x
    x = Component.main()

    def var(s: str) -> AVar:
        return x.Signal(name=s)

    def lvar(s: str) -> LVar:
        return x.LSignal(name=s)

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
    global x
    x = Component.main()

    vars = Vars()
    (va, a) = (var("a"), 2)
    (vb, b) = (var("b"), 3)
    vars.set(va.signal(), a)
    vars.set(vb.signal(), b)

    e1 = (10 + va * vb - 5) * (va**2)
    assert e1.eval(vars) == F((10 + a * b - 5) * (a**2))

    e2 = va - vb
    assert e2.eval(vars) == F(-1)


def test_verify():
    global x
    x = Component.main()

    vars = Vars()
    (va, a) = (var("a"), 2)
    (vb, b) = (var("b"), 3)
    vars.set(va.signal(), a)
    vars.set(vb.signal(), b)

    assert Cond(If(va == 2, Assert(vb == 3))).verify(vars) == True
    assert Cond(If(va == 2, Assert(vb == 4))).verify(vars) == False
    assert Cond(If(va != 2, Assert(vb == 4))).verify(vars) == True

    assert Cond(IfElse(va != 2, Assert(vb == 4), Assert(vb == 3))).verify(vars) == True
    assert Cond(IfElse(va != 2, Assert(vb == 4), Assert(vb != 3))).verify(vars) == False

    assert Assert((va == 2) & (vb == 3)).verify(vars) == True
    assert Assert((va == 5) | (vb == 3)).verify(vars) == True
    assert Assert(~(va == 5)).verify(vars) == True


def IsZero(x: Component) -> Component:
    x = x.Sub("isZero")

    value = x.In(x.Signal())
    is_zero = x.Out(x.LSignal())

    value_inv = x.Signal()
    x.Eq(is_zero, ~(value * value_inv == 1))
    x.Assert((value == 0) | ~is_zero)

    return x.Finalize()


class Word:
    lo: AVar
    hi: AVar
    name: str

    def vars(self) -> List[AVar | LVar]:
        return [self.lo, self.hi]

    def __init__(self, x: Component, name: Optional[str] = None):
        if name is None:
            name = varname(strict=False)
        self.name = name
        self.lo = x.Signal(TypeU128, name=f"{name}_lo")
        self.hi = x.Signal(TypeU128, name=f"{name}_hi")

    def to_64bit_limbs(self, x: Component) -> List[AVar]:
        l0 = x.Signal(TypeU64, name=f"{self.name}_0")
        l1 = x.Signal(TypeU64, name=f"{self.name}_1")
        l2 = x.Signal(TypeU64, name=f"{self.name}_2")
        l3 = x.Signal(TypeU64, name=f"{self.name}_3")
        for limb in [l0, l1, l2, l3]:
            x.Range(limb, TypeU64)
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
    # x.Assign(l0, lambda: w.lo.v().n % 2**64)
    x.Assign(l0, lambda: w.lo.v().n % 2**64)
    x.Assign(l1, lambda: w.lo.v().n // 2**64)
    x.Assign(l2, lambda: w.hi.v().n % 2**64)
    x.Assign(l3, lambda: w.hi.v().n // 2**64)
    for limb in [l0, l1, l2, l3]:
        x.Range(limb, TypeU64)
    x.Assert(w.lo == l0 + l1 * 2**64)
    x.Assert(w.hi == l2 + l3 * 2**64)

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
TypeU64 = Type.Bound(0, F(2**64 - 1))
TypeU128 = Type.Bound(0, F(2**128 - 1))
Type9B = Type.Bound(0, F(2 ** (9 * 8) - 1))
TypeAny = Type.Any()


def test_component():
    x = Component.main()
    a = x.Signal()
    b = x.Signal()
    x.Assert(x.If(a == 13, b != 5))
    [isZero] = IsZero(x).Connect([a])
    x.Assert(isZero)
    [isZero] = IsZero(x).Connect([b])
    x.Assert(isZero)

    x.Assert(a == 0)
    x.Assert(x.If(a == 0, b == 42))

    word_a = Word(x)
    x.Range(word_a.lo, TypeU128)
    x.Range(word_a.hi, TypeU128)
    word_b = Word(x)
    x.Range(word_b.lo, TypeU128)
    x.Range(word_b.hi, TypeU128)
    [res, _] = Add256(x).Connect([word_a, word_b])
    x.Assert((res.lo == 1) & (res.hi == 1))

    dump(x)
    graph(x)


def AddWord(x: Component) -> Component:
    """c, carry = a + b % 2**256"""
    x = x.Sub("addWord")
    a = x.In(Word(x))
    b = x.In(Word(x))
    c = x.Out(Word(x))

    TypeCarry = Type.Bound(0, 1)
    carry_lo = x.Signal(TypeCarry)
    carry_hi = x.Out(x.Signal(TypeCarry))

    x.Assign(carry_lo, lambda: (a.lo.v() + b.lo.v()).n // 2**128)
    x.Assign(carry_hi, lambda: (carry_lo.v() + a.hi.v() + b.hi.v()).n // 2**128)

    x.Eq(c.lo, a.lo + b.lo - carry_lo * 2**128)
    x.Eq(c.hi, carry_lo + a.hi + b.hi - carry_hi * 2**128)
    x.Assert(c.hi == 123)
    x.Range(carry_lo, TypeCarry)
    x.Range(carry_hi, TypeCarry)

    return x.Finalize()


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
    a64s = WordTo64BitLimbs(x, "a_64bits").Connect([a])
    b64s = WordTo64BitLimbs(x, "b_64bits").Connect([b])

    TypeU132 = Type.Bound(0, 2**132 - 1)
    t0 = x.Eq(x.Signal(TypeU132), a64s[0] * b64s[0])
    t1 = x.Eq(x.Signal(TypeU132), a64s[0] * b64s[1] + a64s[1] * b64s[0])
    t2 = x.Eq(x.Signal(TypeU132), a64s[0] * b64s[2] + a64s[1] * b64s[1] + a64s[2] * b64s[0])
    t3 = x.Eq(
        x.Signal(TypeU132),
        a64s[0] * b64s[3] + a64s[1] * b64s[2] + a64s[2] * b64s[1] + a64s[3] * b64s[0],
    )

    carry_lo = x.Signal(Type9B)
    carry_hi = x.Signal(Type9B)
    x.Assign(carry_lo, lambda: (t0.v() + t1.v() * 2**64 + c.lo.v()).n // 2**128)
    x.Assign(carry_hi, lambda: (carry_lo.v() + t2.v() + t3.v() * 2**64 + c.hi.v()).n // 2**128)
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
        + a64s[3] * b64s[3],
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
    x.Range(a.lo, TypeU128)
    x.Range(a.hi, TypeU128)
    b = Word(x)
    x.Range(b.lo, TypeU128)
    x.Range(b.hi, TypeU128)
    c = Word(x)
    x.Range(c.lo, TypeU128)
    x.Range(c.hi, TypeU128)

    mul_add_word = MulAddWord(x)
    print()
    # mul_add_word.type_check()
    [d, carry] = mul_add_word.Connect([a, b, c])
    vars = mul_add_word.WitnessCalc([8, 1, 5, 0, 5, 6])
    for signal_id, value_f in vars.var_map.items():
        print(f"{x.com.signals[signal_id].fullname} = {value_f}")
    for signal_id, value_b in vars.lvar_map.items():
        print(f"{x.com.signals[signal_id].fullname} = {value_b}")
    mul_add_word.Verify()

    # dump(x)


def test_add():
    x = Component.main()

    a = Word(x)
    x.Range(a.lo, TypeU128)
    x.Range(a.hi, TypeU128)
    b = Word(x)
    x.Range(b.lo, TypeU128)
    x.Range(b.hi, TypeU128)

    add_word = AddWord(x)
    print()
    # add_word.type_check()
    [c, carry] = add_word.Connect([a, b])
    vars = add_word.WitnessCalc([1, 2, 3, 4])
    for signal_id, value_f in vars.var_map.items():
        print(f"{x.com.signals[signal_id].fullname} = {value_f}")
    for signal_id, value_b in vars.lvar_map.items():
        print(f"{x.com.signals[signal_id].fullname} = {value_b}")
    add_word.Verify()
