from zktypes.ast import *


def test_aexpr():
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
