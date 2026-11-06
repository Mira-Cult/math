"""Order 17 draft: complement of unary-bounded nondeterministic acceptance.

All integers are mathematical naturals. This complete source is intended for
the paid natural/unary/binary compiler, with no preloaded input or interpreter.
"""


def accept(e, initial, clock):
    h, m = e, 0
    while h % 2:
        m += 1
        h //= 2
    program, radix = h // 2, 4 * (m + 3)
    branch = 0
    while True:
        left, right, state, steps, choices = 0, initial, 2, clock, branch
        while steps:
            if state // 2:
                digit, place = program, 4 * (state - 2) + 2 * (right % 2) + choices % 2
                while place:
                    digit //= radix
                    place -= 1
                digit %= radix
                write, digit = digit % 2, digit // 2
                direction, state = digit % 2, digit // 2
                right //= 2
                if direction:
                    left = 2 * left + write
                else:
                    right = 4 * right + 2 * write + left % 2
                    left //= 2
            choices //= 2
            steps -= 1
        if choices:
            return 0
        if state == 0:
            return 1
        branch += 1
    return 0


def instance(code):
    scan, e = code, 0
    while scan % 2:
        e += 1
        scan //= 2
    if not scan:
        return 0, 0, 0
    scan //= 2
    length = 0
    while scan % 2:
        length += 1
        scan //= 2
    if not scan:
        return 0, 0, 0
    scan //= 2
    scale = 2 ** length
    word = scan % scale
    scan //= scale
    if not scan:
        return 0, 0, 0
    clock = 0
    while scan > 1:
        if scan % 2 == 0:
            return 0, 0, 0
        clock += 1
        scan //= 2
    return e, scale - 1 + 2 * scale * word, clock


def main():
    j = 0
    while True:
        beep()
        i, n, candidate = 1, 0, 1
        while True:
            e, initial, clock = instance(i)
            if accept(e, initial, clock) == accept(j, candidate - 1 + 2 * candidate * (i - candidate), (n + 1) ** j):
                break
            i += 1
            if i >= 2 * candidate:
                candidate *= 2
                n += 1
        j += 1
