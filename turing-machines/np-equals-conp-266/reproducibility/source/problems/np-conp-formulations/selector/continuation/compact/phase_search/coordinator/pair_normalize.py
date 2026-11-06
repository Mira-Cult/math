"""Experimental normalized-prefix source; separate coverage proof required."""

def accept(e, initial, clock):
    branch = 1
    steps = clock
    while steps:
        steps -= 1
        branch *= 2
    while branch:
        branch -= 1
        left, right, state, steps = branch, initial, 1, clock
        while steps:
            steps -= 1
            if state:
                read, right = right % 2, right // 2
                digit, place = e, state + read
                while place:
                    place -= 1
                    state = 0
                    while digit % 2:
                        state += 1
                        digit //= 2
                    digit //= 2
                write, state = state % 2, state // 2
                direction, state = state % 2, state // 2
                if direction:
                    left, right = right, left
                left = 2 * left + write
        if state == 0:
            return 1
    return 0


def main():
    j = 0
    while True:
        beep()
        i = 0
        while True:
            scan, n, e = i, 0, 1
            while True:
                read, scan = scan % 2, scan // 2
                if read == 0:
                    break
                read, scan = scan % 2, scan // 2
                e = 2 * e + read
                n += 1
            if accept(e, 0, n) == accept(j, i, (n + 1) ** j):
                break
            i += 1
        j += 1
