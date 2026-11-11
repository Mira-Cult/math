#!/usr/bin/env python3
"""Exact-integer diagnostic of the conservative FW first-window recurrence.

From the repository root, run with Python 3.11+:
    python3 -B formalizations/sude/scripts/diagnose_fw_first_window_minimum.py

This standalone diagnostic mirrors `fwFirstWindowA`, `fwFirstWindowT`, and
`fwFirstWindowCutoff` in Sude/FWWheelFirstWindowSchedule.lean: it constructs
one ordered period of units modulo 15015, computes each cyclic minimum exactly,
and chooses gap equal to the resulting cutoff at every one of 238 steps.
It uses rational/integer arithmetic only and writes no files. Its output is not
a Lean certificate, an accepted source result, or evidence that the needed
candidate pairs exist. The supplied recurrence is conservative: actual
selected gaps may exceed the cutoff, so this one minimum path cannot rule out
crossing by 238 stages. An all-first-window path is also not the frozen mixed
FW recipe.

The printed first-band upper X is the integer consequence of the existing
RSIndexUpperSharp bound X ≤ (22501/1000) n² with n≤21248. The strict lower X
comparison uses the existing first-band RSIndexLower result X>4·2³⁰. These are
source-bound parameters, not claims that either endpoint is attained.
"""

from fractions import Fraction
from math import gcd

WHEEL = 15015
STAGES = 238
START_RADIUS = 32
ETA = Fraction(3981035, 10000000)
MASS_ZERO = Fraction(403, 10000)
QBAR = Fraction(1, 69780)
UPPER_X = 22501 * 21248**2 // 1000
LOWER_X_STRICT = 4 * 2**30


def main():
    units = [a for a in range(WHEEL) if gcd(a, WHEEL) == 1]
    phi = len(units)
    if phi != 5760 or units[0] != 1:
        raise ValueError('unexpected wheel unit period')
    radius = START_RADIUS
    print(f'wheel={WHEEL} phi={phi} start_radius={radius} stages={STAGES}')
    for j in range(STAGES):
        mass = MASS_ZERO - 2 * QBAR * j
        source_A = ETA * mass * radius - Fraction(1, 2)
        if source_A < 0:
            raise ValueError(f'negative source floor input at stage {j}')
        # Nat.floor of a nonnegative rational is ordinary integer division.
        T = source_A.numerator // source_A.denominator
        quotient, remainder = divmod(T, phi)
        shift = remainder + 1
        # u(i + shift) - u(i), using u(i + phi) = u(i) + WHEEL.
        cyclic_minimum = min(
            units[(i + shift) % phi] + WHEEL * ((i + shift) // phi) - units[i]
            for i in range(phi)
        )
        window_cutoff = quotient * WHEEL + cyclic_minimum
        gap = 2 * min(window_cutoff, radius // 2)
        if gap <= 0 or gap % 2 != 0 or gap > radius:
            raise ValueError(f'invalid minimum gap at stage {j}')
        radius += gap
        if j + 1 in (1, 16, 32, 64, 96, 128, 160, 192, 224, 238):
            print(f'after={j + 1} radius={radius} T={T} gap={gap}')
    target = (UPPER_X + 22) // 23
    print(f'final_radius={radius} 23_times_radius={23 * radius}')
    print(f'first_band_X_upper={UPPER_X} upper_target_ceiling={target}')
    print(f'first_band_X_strict_lower={LOWER_X_STRICT}')
    print(f'below_lower_X_bound={23 * radius < LOWER_X_STRICT}')
    print('Diagnostic only: larger actual selected gaps may cross earlier.')


if __name__ == '__main__':
    main()
