"""Complete normalized NP=coNP source with both existential phases explicit."""

def main():
    j = 0
    while True:
        beep()
        i = 0
        while True:
            scan, n, e = (i, 0, 1)
            while scan % 2:
                scan //= 2
                e *= 2
                if scan % 2:
                    e += 1
                scan //= 2
                n += 1
            scan //= 2
            expected = 0
            branch = e
            while branch:
                branch -= 1
                left = branch
                right = 0
                state = 1
                steps = n
                while steps:
                    steps -= 1
                    if state:
                        state -= 1
                        if right % 2:
                            state += 1
                        right //= 2
                        digit = e
                        while state:
                            state -= 1
                            while digit % 2:
                                digit //= 2
                            digit //= 2
                        state = 0
                        while digit % 2:
                            state += 1
                            digit //= 2
                        digit //= 2
                        write, state = (state % 2, state // 2)
                        if state % 2:
                            left, right = (right, left)
                        state //= 2
                        left = 2 * left + write
                if state == 0:
                    expected = 1
                    break
            e = n
            n = (e + 1) ** j
            e = j
            branch = 1
            steps = n
            while steps:
                steps -= 1
                branch *= 2
            while branch:
                branch -= 1
                left = branch
                right = i
                state = 1
                steps = n
                while steps:
                    steps -= 1
                    if state:
                        state -= 1
                        if right % 2:
                            state += 1
                        right //= 2
                        digit = e
                        while state:
                            state -= 1
                            while digit % 2:
                                digit //= 2
                            digit //= 2
                        state = 0
                        while digit % 2:
                            state += 1
                            digit //= 2
                        digit //= 2
                        write, state = (state % 2, state // 2)
                        if state % 2:
                            left, right = (right, left)
                        state //= 2
                        left = 2 * left + write
                if state == 0:
                    if expected:
                        expected -= 1
                    else:
                        expected = 1
                    break
            if expected == 0:
                break
            i += 1
        j += 1
