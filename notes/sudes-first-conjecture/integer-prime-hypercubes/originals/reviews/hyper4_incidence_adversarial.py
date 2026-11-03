#!/usr/bin/env python3
"""Reviewer-authored SI4 controls: targets selected from equations, not arrays.

Reviewer /root/hyper4_incidence_review, frozen author source b837e307fc41975d0fb332c8215d6835ba47a271.
This finite control supports, and does not replace, the review's uniform proof audit.
"""
from itertools import combinations, product
from pathlib import Path
import json
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "code"))
from hyper4_incidence import integer_lift


def labels(n):
    values = tuple(range(-n // 2 + 1, n // 2 + 1))
    for size in range(1, 5):
        for varying in combinations(range(4), size):
            for tail in product((1, -1), repeat=size - 1):
                for fixed in product(values, repeat=4 - size):
                    yield varying, (1,) + tail, fixed


def equation_targets(n, seed):
    values = tuple(range(-(n // 2), n // 2 + 1))
    nonzero = tuple(v for v in values if v)
    rng = random.Random(seed)
    targets = dict.fromkeys(labels(n), 0)
    matrices = {}
    for pair in combinations(range(4), 2):
        for sign in (1, -1):
            a = {(x, y): rng.randrange(-7, 8) for x in nonzero for y in nonzero}
            for x in nonzero:
                a[x, 0] = -sum(a[x, y] for y in nonzero)
            for y in nonzero:
                a[0, y] = -sum(a[x, y] for x in nonzero)
            a[0, 0] = sum(a[x, y] for x in nonzero for y in nonzero)
            matrices[pair, sign] = a
    for first in ((0, 1), (0, 2), (0, 3)):
        second = tuple(i for i in range(4) if i not in first)
        for sigma, tau in product((1, -1), repeat=2):
            left, right = matrices[first, sigma], matrices[second, tau]
            difference = sum(left[t, tau*t] - right[t, sigma*t] for t in values)
            # A zero-margin matrix with exactly one unit signed trace.
            for i, x in enumerate((1, 2)):
                for j, y in enumerate((sigma, 3*sigma)):
                    right[x, y] += difference * (-1)**(i + j)
    for (pair, sign), a in matrices.items():
        for fixed, value in a.items():
            targets[pair, (1, sign), fixed] = value
    for triple in combinations(range(4), 3):
        for signs in product((1, -1), repeat=2):
            data = {x: rng.randrange(-20, 21) for x in nonzero}
            data[0] = -sum(data.values())
            for x, value in data.items():
                targets[triple, (1,) + signs, (x,)] = value
    for signs in product((1, -1), repeat=3):
        targets[(0, 1, 2, 3), (1,) + signs, ()] = rng.randrange(-100, 101)
    return targets


def check_actual_image(n, array, targets):
    values = range(-(n // 2), n // 2 + 1)
    for (varying, signs, fixed), wanted in targets.items():
        rest = tuple(i for i in range(4) if i not in varying)
        actual = 0
        for t in values:
            point = [0]*4
            for i, value in zip(rest, fixed):
                point[i] = value
            for i, sign in zip(varying, signs):
                point[i] = sign*t
            actual += array.get(tuple(point), 0)
        if actual != wanted:
            raise AssertionError((n, varying, signs, fixed, actual, wanted))


def main():
    results = []
    for n in (17, 19, 21):
        target = equation_targets(n, 20261102 + n)
        lift = integer_lift(n, target)
        check_actual_image(n, lift, target)
        assert sum(lift.values()) == 0
        results.append({"n": n, "lines": len(target), "nonzero_lift_cells": len(lift)})
    n, residue, modulus = 17, 3, 17
    target = equation_targets(n, 20261234)
    adjusted = {key: modulus*value+n*residue for key, value in target.items()}
    lift = integer_lift(n, adjusted, residue=residue, modulus=modulus)
    check_actual_image(n, lift, adjusted)
    assert len(lift) == n**4 and all((x-residue) % modulus == 0 for x in lift.values())
    print(json.dumps({"status": "passed", "equation_selected_targets": results,
                      "entry_congruence": {"n": n, "modulus": modulus, "residue": residue},
                      "scope": "finite signed integer lifts; no prime or permutation conclusion"}, sort_keys=True))


if __name__ == "__main__":
    main()
