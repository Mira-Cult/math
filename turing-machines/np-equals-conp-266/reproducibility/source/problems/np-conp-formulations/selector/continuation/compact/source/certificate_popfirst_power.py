"""New complete-source experiment; proof and independent acceptance are separate."""

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
        i, n, candidate, initial = 1, 0, 1, 0
        while True:
            if accept(i, 0, n) == accept(j, initial, (n + 1) ** j):
                break
            i += 1
            if i >= 2 * candidate:
                candidate *= 2
                n += 1
                initial = candidate - 1
            else:
                initial += 2 * candidate
        j += 1
