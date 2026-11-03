"""Alternative complete P=NP source: a clocked universal NP reference language.

Every candidate is deterministic (choice zero).  Reference membership uses
bounded nondeterministic choices.  Compare equality, not complementation.
"""

def accept(e, initial, clock, branches):
    while branches:
        branches -= 1
        left, right, state, steps, choices = (0, initial, 1, clock, branches)
        read, right = (right % 2, right // 2)
        while steps:
            steps -= 1
            choice, choices = (choices % 2, choices // 2)
            digit, place = (e, state + 2 * read + choice)
            while place:
                place -= 1
                state = 0
                while digit % 2:
                    state += 1
                    digit //= 2
                digit //= 2
            write, state = (state % 2, state // 2)
            direction, state = (state % 2, state // 2)
            if direction:
                left, right = (right, left)
            left = 2 * left + write
            read, right = (right % 2, right // 2)
            if state == 0:
                return 1
    return 0

def main():
    program, exponent = (0, 1)
    while True:
        beep()
        n, radix, remaining = (0, 1, 0)
        while True:
            expected = 0
            branches = radix
            while branches:
                branches -= 1
                left = 0
                right = 0
                state = 0
                steps = n
                choices = branches
                while steps:
                    steps -= 1
                    if choices % 2:
                        state += 1
                    choices //= 2
                    digit = radix + remaining
                    while state:
                        state -= 1
                        while digit % 2:
                            digit //= 2
                        digit //= 2
                    write, direction, state = (0, 0, 0)
                    while digit % 2:
                        digit //= 2
                        if write:
                            write = 0
                            if direction:
                                direction = 0
                                state += 1
                            else:
                                direction = 1
                        else:
                            write = 1
                    digit //= 2
                    if direction:
                        direction = 0
                        left, right = (right, left)
                    left *= 2
                    if write:
                        write = 0
                        left += 1
                    if state:
                        state -= 1
                        if right % 2:
                            state += 2
                        right //= 2
                    else:
                        right //= 2
                        expected = 1
                        branches = 0
                        break
            steps = (n + 2) ** exponent
            left = 0
            state = 0
            right = remaining * radix
            right = 2 * right + radix
            right -= 1
            if right % 2:
                state += 2
            right //= 2
            while steps:
                steps -= 1
                digit = program
                while state:
                    state -= 1
                    while digit % 2:
                        digit //= 2
                    digit //= 2
                write, direction, state = (0, 0, 0)
                while digit % 2:
                    digit //= 2
                    if write:
                        write = 0
                        if direction:
                            direction = 0
                            state += 1
                        else:
                            direction = 1
                    else:
                        write = 1
                digit //= 2
                if direction:
                    direction = 0
                    left, right = (right, left)
                left *= 2
                if write:
                    write = 0
                    left += 1
                if state:
                    state -= 1
                    if right % 2:
                        state += 2
                    right //= 2
                else:
                    right //= 2
                    if expected:
                        expected = 0
                    else:
                        expected = 1
                    break
            if expected:
                break
            if remaining:
                remaining -= 1
            else:
                radix *= 2
                n += 1
                remaining = radix
                remaining -= 1
        if program:
            program -= 1
            exponent += 1
        else:
            program = exponent
            exponent = 1
