from zktypes.ast import AExpr, Var, F, Cond, If, IfElse, Assert, StrVar


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
