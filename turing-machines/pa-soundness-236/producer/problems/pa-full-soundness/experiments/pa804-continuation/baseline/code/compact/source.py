"""All-rank soundness producer for the PA238 compact calculus K.

Finite postfix certificates, total HF matrix evaluation, and the fixed unary
record observer. This source is in the already-reviewed NaturalBuilder subset.
The theorem identifying K soundness with PA soundness is external mathematics.
"""


def pair(a, b):
    s = a + b
    return s * (s + 1) // 2 + b


def unpair(z):
    w = 0
    while z > w:
        w += 1
        z -= w
    return w - z, z


def cons(a, b):
    return pair(a, b) + 1


def pop(s):
    if s == 0:
        return 0, 0
    a, b = unpair(s - 1)
    return a, b


def imp(a, b):
    return 4 * pair(a, b)


def member(a, b):
    return 4 * pair(a, b) + 1


def all_(a, b):
    return 4 * pair(a, b) + 2


def equal(a, b):
    return 4 * pair(a, b) + 3


def neg(a):
    return imp(a, 1)


def exists(a, b):
    return neg(all_(a, neg(b)))


def both(a, b):
    return neg(imp(a, neg(b)))


def axiom(selector, a, b, c, u):
    if selector == 0:
        return exists(a, equal(a, b))
    if selector == 1:
        return imp(all_(a, imp(b, c)), imp(all_(a, b), all_(a, c)))
    if selector == 2:
        return imp(member(a, b), imp(equal(b, c), member(a, c)))
    if selector == 3:
        return imp(all_(a, all_(b, c)), all_(b, all_(a, c)))
    if selector == 4:
        return imp(equal(a, b), imp(member(a, c), member(b, c)))
    if selector == 5:
        return imp(exists(a, all_(a, b)), b)
    if selector == 6:
        return imp(equal(a, b), imp(equal(a, c), equal(b, c)))
    if selector == 7:
        return imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c)))
    if c == a or c == b:
        return 0
    return both(exists(c, both(all_(b, both(imp(member(a, b), imp(c, member(c, b))),
                                                imp(member(c, b), c))),
                                    imp(c, member(c, b)))),
                both(imp(equal(a, b), all_(c, equal(a, b))),
                     imp(member(a, b), all_(c, member(a, b)))))


def theorem(p):
    # Missing stack entries are truth. Commands are cons-encoded natural lists.
    # opcode 0 AX, 1 GEN, 2 MP, 3 DROP; every command sequence is sound.
    t = 0
    stack = 0
    while p > 0:
        command, p = pop(p)
        op = command % 4
        data = command // 4
        if op == 0:
            selector = data % 9
            a, data = unpair(data // 9)
            b, data = unpair(data)
            c, u = unpair(data)
            stack = pair(t, stack)
            t = axiom(selector, a, b, c, u)
        elif op == 1:
            t = all_(data, t)
        elif op == 2:
            a, stack = unpair(stack)
            if t % 4 == 0:
                left, right = unpair(t // 4)
                if left == a:
                    t = right
                else:
                    t = 0
            else:
                t = 0
        else:
            t, stack = unpair(stack)
    return t


def lookup(env, x):
    # Newest binding first: repeated prefix variables have ordinary shadowing.
    while env > 0:
        binding, env = unpair(env)
        y, value = unpair(binding)
        if y == x:
            return value
    return 0


def matrix(f, env):
    # Return (well-formed QF flag, truth). Every natural is a formula, but a
    # universal below the prefix makes this certificate unsuitable for a rank.
    todo = cons(2 * f, 0)
    values = 0
    while todo > 0:
        task, todo = pop(todo)
        if task == 1:
            b, values = unpair(values)
            a, values = unpair(values)
            v = 0
            if a == 0 or b != 0:
                v = 1
            values = pair(v, values)
        else:
            f = task // 2
            if f == 0:
                values = pair(1, values)
            else:
                tag = f % 4
                a, b = unpair(f // 4)
                if tag == 0:
                    todo = cons(2 * a, cons(2 * b, cons(1, todo)))
                elif tag == 2:
                    return 0, 0
                else:
                    a = lookup(env, a)
                    b = lookup(env, b)
                    if tag == 1:
                        while b > 0:
                            a //= 2
                            b -= 1
                        v = a % 2
                    else:
                        v = 0
                        if a == b:
                            v = 1
                    values = pair(v, values)
    v, values = unpair(values)
    return 1, v


def record(n, p, xs):
    # Free variables use value 0. Sentence soundness implies every theorem's
    # universal closure and hence truth under this environment. Closed normal
    # forms still supply complete counterexample coverage.
    f = theorem(p)
    env = 0
    i = 0
    while i < n:
        if xs == 0:
            return 0
        value, xs = pop(xs)
        if i % 2 == 0:
            # exists x B abbreviates imp(all(x,imp(B,1)),1).
            if f % 4 != 0:
                return 0
            f, end = unpair(f // 4)
            if end != 1 or f % 4 != 2:
                return 0
            x, f = unpair(f // 4)
            if f % 4 != 0:
                return 0
            f, end = unpair(f // 4)
            if end != 1:
                return 0
        else:
            if f % 4 != 2:
                return 0
            x, f = unpair(f // 4)
        env = pair(pair(x, value), env)
        i += 1
    if xs != 0:
        return 0
    valid, truth = matrix(f, env)
    if valid != 0 and truth == 0:
        return 1
    return 0


def emit_natural(value):
    while value > 0:
        emit1()
        value -= 1
    emit0()
    return 0


def main():
    stage = 0
    while True:
        rank, rest = unpair(stage)
        rank += 1
        proof, rest = unpair(rest)
        backwards = 0
        remaining = rank
        while remaining > 0:
            value, rest = unpair(rest)
            backwards = cons(value, backwards)
            remaining -= 1
        values = 0
        while backwards > 0:
            value, backwards = pop(backwards)
            values = cons(value, values)
        bit = record(rank, proof, values)
        ignored = emit_natural(rank)
        ignored = emit_natural(proof)
        remaining = values
        while remaining > 0:
            value, remaining = pop(remaining)
            ignored = emit_natural(value)
        ignored = emit_natural(bit)
        stage += 1
