#!/usr/bin/env python3
"""Independent exact first-odd-prime full signed-line cube checker.

This module imports no construction or incidence module. It builds lines
from subsets of varying coordinates and independently trial-generates the
entry pool. A passing finite certificate does not prove an asymptotic tail.
"""

from __future__ import annotations

import argparse
from copy import deepcopy
from itertools import combinations, product
import json
from math import isqrt
from pathlib import Path


def prime(value):
    if type(value) is not int or value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    return all(value % d for d in range(3, isqrt(value) + 1, 2))


def odd_prime_pool(count):
    answer = []
    candidate = 3
    while len(answer) < count:
        if prime(candidate):
            answer.append(candidate)
        candidate += 2
    return answer


def full_lines(n):
    if type(n) is not int or n < 1 or n % 2 == 0:
        raise ValueError("Require a positive odd side length")
    lines = set()
    axes = (0, 1, 2)
    for number_varying in (1, 2, 3):
        for varying in combinations(axes, number_varying):
            fixed = tuple(d for d in axes if d not in varying)
            for fixed_values in product(range(n), repeat=len(fixed)):
                # Reversing all parameters gives the same subset; normalize
                # the first varying coordinate to increase with t.
                for reversals in product((False, True), repeat=number_varying - 1):
                    reverse = dict(zip(varying[1:], reversals))
                    cells = []
                    for t in range(n):
                        point = dict(zip(fixed, fixed_values))
                        for d in varying:
                            point[d] = n - 1 - t if reverse.get(d, False) else t
                        cells.append((point[0] * n + point[1]) * n + point[2])
                    lines.add(tuple(sorted(cells)))
    expected = 1 if n == 1 else 3 * n * n + 6 * n + 4
    if len(lines) != expected or any(len(set(line)) != n for line in lines):
        raise AssertionError("Independent geometric count failed")
    return tuple(sorted(lines))


def verify(certificate):
    if not isinstance(certificate, dict) or certificate.get("kind") != "prime-array-exact-pool":
        raise ValueError("Wrong certificate type")
    specification = certificate["spec"]
    n = specification["n"]
    lines = full_lines(n)
    if (type(specification.get("dimension")) is not int or specification["dimension"] != 3
            or specification.get("family") != "signed_lines"):
        raise ValueError("Require the full signed-line three-dimensional family")
    pool_spec = specification["pool"]
    if (pool_spec.get("kind") != "consecutive_odd_primes"
            or type(pool_spec.get("offset")) is not int or pool_spec["offset"] != 0
            or type(pool_spec.get("count")) is not int or pool_spec["count"] != n ** 3):
        raise ValueError("Require exactly the first n^3 odd primes")
    if certificate.get("entry_order") != "lexicographic":
        raise ValueError("Require lexicographic cell indexing")
    values = certificate["values"]
    expected_pool = odd_prime_pool(n ** 3)
    if (not isinstance(values, list) or any(type(v) is not int for v in values)
            or sorted(values) != expected_pool):
        raise ValueError("Entry omitted, repeated, nonprime, or outside the pool")
    records = certificate["constraints"]
    if not isinstance(records, list) or len(records) != len(lines):
        raise ValueError("Missing or additional line")
    supplied = {}
    for record in records:
        cells = record["cells"]
        if (not isinstance(cells, list) or len(cells) != n
                or any(type(c) is not int or not 0 <= c < n ** 3 for c in cells)):
            raise ValueError("Invalid cell indexing")
        line = tuple(cells)
        if line != tuple(sorted(set(line))) or line in supplied:
            raise ValueError("Noncanonical or repeated line")
        if type(record["sum"]) is not int:
            raise ValueError("Line sum must be an integer")
        supplied[line] = record["sum"]
    if set(supplied) != set(lines):
        raise ValueError("A line is omitted or misidentified")
    sums = []
    for line in lines:
        actual = sum(values[c] for c in line)
        if actual != supplied[line]:
            raise ValueError("Cached sum differs from the actual array")
        if not prime(actual):
            raise ValueError("A required line sum is composite")
        sums.append(actual)
    return {"n": n, "entries": len(values), "lines": len(lines),
            "total": sum(values), "distinct_prime_sums": len(set(sums)),
            "status": "VERIFIED_EXACT_POOL_FULL_SIGNED_CUBE"}


def rejected_controls(certificate):
    bad = []
    trial = deepcopy(certificate)
    trial["values"][0] = 9
    bad.append(trial)
    trial = deepcopy(certificate)
    if len(trial["values"]) > 1:
        trial["values"][0] = trial["values"][1]
    else:
        trial["values"].append(3)
    bad.append(trial)
    trial = deepcopy(certificate)
    trial["constraints"].pop()
    bad.append(trial)
    trial = deepcopy(certificate)
    trial["constraints"][0]["sum"] += 2
    bad.append(trial)
    trial = deepcopy(certificate)
    def is_diagonal(cells):
        n = trial["spec"]["n"]
        points = [(c // (n * n), (c // n) % n, c % n) for c in cells]
        return sum(len({p[d] for p in points}) > 1 for d in range(3)) >= 2
    record = next((r for r in trial["constraints"] if is_diagonal(r["cells"])),
                  trial["constraints"][0])
    line = record["cells"]
    if len(trial["values"]) > 1:
        replacement = next(c for c in range(len(trial["values"])) if c not in line)
        line[-1] = replacement
        line.sort()
        record["sum"] = sum(trial["values"][c] for c in line)
    else:
        trial["constraints"][0]["cells"] = [1]
    bad.append(trial)
    trial = deepcopy(certificate)
    trial["spec"]["pool"]["offset"] = 1
    bad.append(trial)
    for trial in bad:
        try:
            verify(trial)
        except (ValueError, TypeError, KeyError, IndexError):
            continue
        raise AssertionError("A corrupted certificate was accepted")
    return len(bad)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="+")
    parser.add_argument("--negative-controls", action="store_true")
    args = parser.parse_args()
    results = []
    rejected = 0
    for name in args.files:
        certificate = json.loads(Path(name).read_text())
        results.append({"file": Path(name).name, **verify(certificate)})
        if args.negative_controls:
            rejected += rejected_controls(certificate)
    print(json.dumps({"certificates": results, "negative_controls_rejected": rejected,
                      "scope": "Finite certificates only; no asymptotic inference."}, indent=2))


if __name__ == "__main__":
    main()
