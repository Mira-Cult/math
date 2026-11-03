#!/usr/bin/env python3
"""Exact finite controls for hyper4_targets.md; no entry arrangement is claimed.

The certificate producer uses canonical varying-coordinate descriptions.
The verifier independently enumerates all four-coordinate parameter choices,
deduplicates their cell sets, and checks every partition identity. Prime
generation uses a sieve; certificate primality and the exact initial pool
are independently checked by trial division. Only Python's standard library
is required. These finite checks do not verify the asymptotic FL hypotheses.
"""

from __future__ import annotations

import argparse
from collections import Counter
import copy
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
import json
from math import gcd, isqrt
from pathlib import Path


KIND = "hyper4_prime_target_vector_v1"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sieve(limit: int) -> list[int]:
    flags = bytearray(b"\x01") * (limit + 1)
    flags[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            flags[p * p : limit + 1 : p] = b"\x00" * (
                (limit - p * p) // p + 1
            )
    return [p for p in range(2, limit + 1) if flags[p]]


def producer_pool(n: int) -> list[int]:
    limit = max(64, 4 * n**4)
    while True:
        primes = sieve(limit)[1:]
        if len(primes) >= n**4:
            return primes[: n**4]
        limit *= 2


def is_prime_by_division(value: int) -> bool:
    if value < 2:
        return False
    if value % 2 == 0:
        return value == 2
    for divisor in range(3, isqrt(value) + 1, 2):
        if value % divisor == 0:
            return False
    return True


def checker_pool(n: int) -> list[int]:
    answer: list[int] = []
    candidate = 3
    while len(answer) < n**4:
        if is_prime_by_division(candidate):
            answer.append(candidate)
        candidate += 2
    return answer


def pool_digest(pool: list[int]) -> str:
    return sha256((",".join(map(str, pool)) + "\n").encode()).hexdigest()


def label_sets(m: int) -> list[tuple[int, ...]]:
    return [
        labels
        for size in range(1, min(3, m + 1) + 1)
        for labels in combinations(range(m + 1), size)
    ]


def weight(labels: tuple[int, ...]) -> int:
    if len(labels) == 1:
        return 1 if labels == (0,) else 8
    if len(labels) == 2:
        return 18 if 0 in labels else 48
    if len(labels) == 3:
        return 24 if 0 in labels else 48
    raise ValueError("unsupported label set")


def nearest_in_class(center: Fraction, residue: int, modulus: int) -> int:
    """Return the closest integer in one class, taking the smaller in a tie."""
    residue %= modulus
    scaled = (center - residue) / modulus
    lower = scaled.numerator // scaled.denominator
    choices = (residue + modulus * lower, residue + modulus * (lower + 1))
    return min(choices, key=lambda value: (abs(value - center), value))


def finishing_totals(m: int, total: int, bulk: int, center_prime: int):
    residual = total - bulk - center_prime
    require(residual % 4 == (26 * m) % 4, "center parity repair failed")
    mu = Fraction(total, (2 * m + 1) ** 3)
    s18 = nearest_in_class(m * mu, residual // 2 - 4 * m, 8)
    numerator = residual // 2 - 9 * s18
    require(numerator % 4 == 0, "nonintegral finishing total")
    s8 = numerator // 4
    require(s8 % 2 == s18 % 2 == m % 2, "wrong finishing parity")
    require(8 * s8 + 18 * s18 == residual, "wrong weighted finish")
    return residual, s8, s18


def radius_floor(total: int, n: int) -> int:
    """floor((total/n^3)^(3/5)), with exact integer comparisons."""
    lower, upper = 0, 1
    while upper**5 * n**9 <= total**3:
        upper *= 2
    while upper - lower > 1:
        middle = (lower + upper) // 2
        if middle**5 * n**9 <= total**3:
            lower = middle
        else:
            upper = middle
    return lower


def finite_prime_list(length: int, total: int, primes: list[int]):
    """Bounded exact search only; failure does not assert nonexistence."""
    available = set(primes)
    if length == 1:
        return [total] if total in available else None
    if length == 2:
        for first in primes:
            if total - first in available:
                return [first, total - first]
        return None
    for repeated in sorted(primes, key=lambda p: (abs(length * p - total), p)):
        remaining = total - (length - 2) * repeated
        for first in primes:
            if remaining - first in available:
                return [repeated] * (length - 2) + [first, remaining - first]
    return None


def construct_variables(n: int, pool: list[int]):
    """Finite witness search inspired by HW, not an implementation of FL."""
    m = (n - 1) // 2
    total = sum(pool)
    mu = Fraction(total, n**3)
    radius = radius_floor(total, n)
    lower = max(3, (mu - radius).__ceil__())
    upper = (mu + radius).__floor__()
    nearby = [p for p in sieve(upper) if p >= lower]
    below = max(p for p in nearby if p < mu)
    above = min(p for p in nearby if p > mu)
    variables: dict[tuple[int, ...], int] = {}
    discrepancy = Fraction(0)
    for labels in label_sets(m):
        if weight(labels) not in (24, 48):
            continue
        chosen = below if discrepancy >= 0 else above
        variables[labels] = chosen
        discrepancy += weight(labels) * (chosen - mu)
    bulk = sum(weight(labels) * p for labels, p in variables.items())
    centers = sorted(
        (p for p in nearby if p % 4 == (total - 26 * m) % 4),
        key=lambda p: (abs(p - mu), p),
    )
    for center in centers:
        residual, _, closest18 = finishing_totals(m, total, bulk, center)
        # A finite witness may need another member of this class. This
        # enumeration is not used in HW, where FL handles the nearest one.
        min18, max18 = m * nearby[0], m * nearby[-1]
        candidates = range(
            closest18 + 8 * ((min18 - closest18 + 7) // 8), max18 + 1, 8
        )
        for s18 in sorted(candidates, key=lambda s: (abs(s - m * mu), s)):
            numerator = residual // 2 - 9 * s18
            if numerator % 4:
                continue
            s8 = numerator // 4
            list8 = finite_prime_list(m, s8, nearby)
            if list8 is None:
                continue
            list18 = finite_prime_list(m, s18, nearby)
            if list18 is None:
                continue
            variables[(0,)] = center
            for a, p in enumerate(list8, 1):
                variables[(a,)] = p
            for a, p in enumerate(list18, 1):
                variables[(0, a)] = p
            require(
                sum(weight(labels) * p for labels, p in variables.items())
                == total,
                "producer weighted total failed",
            )
            return variables
    raise RuntimeError("finite target search exhausted its stated window")


def producer_lines(n: int, variables: dict[tuple[int, ...], int], modulus: int):
    m = (n - 1) // 2
    lines = []
    for size in range(1, 5):
        for varying in combinations(range(4), size):
            fixed = [axis for axis in range(4) if axis not in varying]
            for tail in product((-1, 1), repeat=size - 1):
                direction = [0] * 4
                for axis, sign in zip(varying, (1,) + tail):
                    direction[axis] = sign
                for coordinates in product(range(-m, m + 1), repeat=len(fixed)):
                    base = [0] * 4
                    for axis, coordinate in zip(fixed, coordinates):
                        base[axis] = coordinate
                    labels = tuple(sorted({abs(value) for value in coordinates}))
                    target = variables[labels or (0,)]
                    lines.append(
                        {"direction": direction.copy(), "base": base,
                         "target": target, "residue": target % modulus}
                    )
    return lines


def make_certificate(n: int, modulus: int = 2) -> dict:
    require(n >= 3 and n % 2 == 1, "use an odd order at least 3")
    pool = producer_pool(n)
    variables = construct_variables(n, pool)
    return {
        "kind": KIND,
        "n": n,
        "scope": "prime line targets only; no entry arrangement",
        "pool": {"count": n**4, "largest": pool[-1], "total": sum(pool),
                 "sha256": pool_digest(pool)},
        "modulus": modulus,
        "prime_variables": [
            {"labels": list(labels), "value": variables[labels]}
            for labels in label_sets((n - 1) // 2)
        ],
        "lines": producer_lines(n, variables, modulus),
    }


def cell_number(point: tuple[int, ...], n: int) -> int:
    m = (n - 1) // 2
    number = 0
    for value in point:
        number = number * n + value + m
    return number


def independent_full_line_sets(n: int) -> set[tuple[int, ...]]:
    """Direct parameter-option enumeration; no producer descriptors reused."""
    m = (n - 1) // 2
    choices = [(False, fixed) for fixed in range(-m, m + 1)]
    choices += [(True, 1), (True, -1)]
    lines: set[tuple[int, ...]] = set()
    for choices_at_axes in product(choices, repeat=4):
        if not any(varying for varying, _ in choices_at_axes):
            continue
        cells = []
        for parameter in range(-m, m + 1):
            point = tuple(
                value * parameter if varying else value
                for varying, value in choices_at_axes
            )
            cells.append(cell_number(point, n))
        lines.add(tuple(sorted(cells)))
    return lines


def reconstruct_pattern_lines(n: int, line_sets: set[tuple[int, ...]],
                              variables: dict, modulus: int) -> list[dict]:
    """Decode an explicitly declared set-pattern certificate from cell sets.

    This verifier path does not call the producer's line constructor. Compact
    certificates specify the whole family by a rule, not by an incomplete
    selected list; literal certificates remain available for omission tests.
    """
    m = (n - 1) // 2
    result = []
    for cells in sorted(line_sets):
        points = []
        for number in cells:
            point = [0] * 4
            for axis in range(3, -1, -1):
                number, remainder = divmod(number, n)
                point[axis] = remainder - m
            points.append(point)
        axis_values = [set(point[axis] for point in points) for axis in range(4)]
        varying = [axis for axis in range(4) if len(axis_values[axis]) > 1]
        endpoint = next(point for point in points if point[varying[0]] == m)
        direction = [0] * 4
        base = [0] * 4
        for axis in range(4):
            if axis in varying:
                direction[axis] = endpoint[axis] // m
            else:
                base[axis] = next(iter(axis_values[axis]))
        labels = tuple(sorted({abs(base[axis]) for axis in range(4)
                               if axis not in varying}))
        target = variables[labels or (0,)]
        result.append({"direction": direction, "base": base, "target": target,
                       "residue": target % modulus})
    return result


def check_partition_identities(n: int, targets: dict) -> int:
    m = (n - 1) // 2
    interval = range(-m, m + 1)
    checked = 0
    for mask_a in range(1, 16):
        a = [axis for axis in range(4) if mask_a >> axis & 1]
        for mask_b in range(mask_a + 1, 16):
            if mask_a & mask_b:
                continue
            b = [axis for axis in range(4) if mask_b >> axis & 1]
            c = [axis for axis in range(4) if axis not in a + b]
            for tail_a in product((-1, 1), repeat=len(a) - 1):
                sigma = (1,) + tail_a
                direction_a = [0] * 4
                for axis, sign in zip(a, sigma):
                    direction_a[axis] = sign
                for tail_b in product((-1, 1), repeat=len(b) - 1):
                    tau = (1,) + tail_b
                    direction_b = [0] * 4
                    for axis, sign in zip(b, tau):
                        direction_b[axis] = sign
                    for fixed in product(interval, repeat=len(c)):
                        left = right = 0
                        for parameter in interval:
                            base_a = [0] * 4
                            base_b = [0] * 4
                            for axis, value in zip(c, fixed):
                                base_a[axis] = base_b[axis] = value
                            for axis, sign in zip(b, tau):
                                base_a[axis] = sign * parameter
                            for axis, sign in zip(a, sigma):
                                base_b[axis] = sign * parameter
                            left += targets[(tuple(direction_a), tuple(base_a))]
                            right += targets[(tuple(direction_b), tuple(base_b))]
                        require(
                            left == right,
                            f"partition identity failed: {a}, {b}, {fixed}",
                        )
                        checked += 1
    require(checked == 6 * n**2 + 24 * n + 28, "identity count mismatch")
    return checked


def check_certificate(certificate: dict) -> dict:
    require(certificate.get("kind") == KIND, "not a target-vector certificate")
    n = certificate["n"]
    require(type(n) is int and n >= 3 and n % 2 == 1, "invalid order")
    m = (n - 1) // 2
    pool = checker_pool(n)
    pool_data = certificate["pool"]
    require(pool_data["count"] == len(pool), "wrong pool count")
    require(pool_data["largest"] == pool[-1], "wrong largest pool prime")
    require(pool_data["total"] == sum(pool), "wrong exact pool total")
    require(pool_data["sha256"] == pool_digest(pool), "wrong exact pool digest")
    total = sum(pool)
    modulus = certificate["modulus"]
    require(type(modulus) is int and modulus >= 2 and modulus % 2 == 0,
            "invalid modulus")
    require(modulus <= 16 * (pool[-1] - 1).bit_length(), "modulus out of range")

    variables = {}
    for entry in certificate["prime_variables"]:
        labels = tuple(entry["labels"])
        require(labels not in variables, "duplicate prime variable")
        require(labels == tuple(sorted(set(labels))), "noncanonical label set")
        variables[labels] = entry["value"]
    require(set(variables) == set(label_sets(m)), "missing or extra prime variable")
    for value in variables.values():
        require(type(value) is int and is_prime_by_division(value),
                "composite prime variable")

    weights = Counter(
        tuple(sorted({abs(x), abs(y), abs(z)}))
        for x, y, z in product(range(-m, m + 1), repeat=3)
    )
    require(all(weights[labels] == weight(labels) for labels in variables),
            "weight formula mismatch")
    require(sum(weights.values()) == n**3, "wrong total weight")
    require(sum(weights[labels] * value for labels, value in variables.items())
            == total, "wrong weighted exact total")

    expected = independent_full_line_sets(n)
    require(len(expected) == 4 * n**3 + 12 * n**2 + 16 * n + 8,
            "independent line count failed")
    if "line_rule" in certificate:
        require(certificate["line_rule"] == "absolute_coordinate_set",
                "unknown compact target rule")
        require("lines" not in certificate, "ambiguous literal and compact targets")
        line_entries = reconstruct_pattern_lines(n, expected, variables, modulus)
    else:
        line_entries = certificate["lines"]
    actual: set[tuple[int, ...]] = set()
    targets = {}
    for entry in line_entries:
        direction, base = tuple(entry["direction"]), tuple(entry["base"])
        require(len(direction) == len(base) == 4, "wrong descriptor dimension")
        require(all(type(d) is int and d in (-1, 0, 1) for d in direction),
                "invalid direction")
        varying = [axis for axis in range(4) if direction[axis]]
        require(varying and direction[varying[0]] == 1,
                "direction is not canonically oriented")
        require(all(type(value) is int and -m <= value <= m for value in base),
                "invalid fixed coordinate")
        require(all(base[axis] == 0 for axis in varying), "hidden varying offset")
        cells = tuple(sorted(
            cell_number(tuple(base[a] + direction[a] * t for a in range(4)), n)
            for t in range(-m, m + 1)
        ))
        require(cells not in actual, "duplicate line")
        require(cells in expected, "line is not a full signed-coordinate line")
        actual.add(cells)
        value = entry["target"]
        require(type(value) is int and is_prime_by_division(value),
                "composite line target")
        require(value % 2 == 1, "even prime target")
        require(abs(value * n**3 - total)**5 <= total**3 * n**6,
                "target outside the exact power window")
        require(gcd(value, modulus) == 1, "nonunit target residue")
        require(entry["residue"] == value % modulus, "target residue mismatch")
        targets[(direction, base)] = value
    require(actual == expected, "omitted or extra required line")
    identity_count = check_partition_identities(n, targets)

    for (direction, base), value in targets.items():
        labels = tuple(sorted({abs(base[a]) for a in range(4) if not direction[a]}))
        require(value == variables[labels or (0,)], "target violates set pattern")
    for axis in range(4):
        direction = tuple(int(a == axis) for a in range(4))
        directional_total = sum(
            value for (varying, _), value in targets.items() if varying == direction
        )
        require(directional_total == total, "wrong directional grand total")
    return {
        "n": n,
        "lines": len(actual),
        "partition_identities": identity_count,
        "prime_variables": len(variables),
        "pool_count": len(pool),
        "pool_total": total,
        "scope": "target vector; not an entry arrangement",
        "small_order_integer_image_claim": False if n < 17 else "uses SI4",
    }


def arithmetic_controls() -> None:
    for m in range(1, 33):
        n = 2 * m + 1
        counts = Counter(
            tuple(sorted({abs(x), abs(y), abs(z)}))
            for x, y, z in product(range(-m, m + 1), repeat=3)
        )
        require(set(counts) == set(label_sets(m)), "weight keys failed")
        require(sum(counts.values()) == n**3, "weight sum failed")
        require(all(value == weight(labels) for labels, value in counts.items()),
                "explicit weight enumeration failed")
        for total in (n**3 + 2, 27 * n**3 + 4, 1001 * n**3 + 8):
            for bulk in (0, 24, 48, 72, 120):
                center = (total - 26 * m) % 4
                residual, s8, s18 = finishing_totals(m, total, bulk, center)
                require(8 * s8 + 18 * s18 == residual, "weighted arithmetic failed")
                require(s8 % 2 == s18 % 2 == m % 2, "parity arithmetic failed")
                require(abs(s18 - Fraction(m * total, n**3)) <= 4,
                        "residue rounding exceeded four")


def negative_controls(certificate: dict) -> list[str]:
    if "line_rule" in certificate:
        certificate = copy.deepcopy(certificate)
        n, modulus = certificate["n"], certificate["modulus"]
        variables = {tuple(entry["labels"]): entry["value"]
                     for entry in certificate["prime_variables"]}
        certificate["lines"] = reconstruct_pattern_lines(
            n, independent_full_line_sets(n), variables, modulus
        )
        del certificate["line_rule"]
    rejected = []

    def expect(name: str, damaged: dict, phrase: str):
        try:
            check_certificate(damaged)
        except ValueError as error:
            require(phrase in str(error), f"{name}: unexpected rejection: {error}")
            rejected.append(name)
        else:
            raise ValueError(f"negative control accepted: {name}")

    damaged = copy.deepcopy(certificate)
    damaged["pool"]["total"] += 2
    expect("changed_pool_total", damaged, "exact pool total")

    damaged = copy.deepcopy(certificate)
    damaged["lines"].pop()
    expect("omitted_line", damaged, "omitted")

    damaged = copy.deepcopy(certificate)
    damaged["lines"].append(copy.deepcopy(damaged["lines"][0]))
    expect("duplicated_line", damaged, "duplicate line")

    damaged = copy.deepcopy(certificate)
    damaged["lines"][0]["target"] = 9
    expect("composite_target", damaged, "composite line target")

    damaged = copy.deepcopy(certificate)
    damaged["lines"][0]["residue"] = 0
    expect("invalid_residue", damaged, "residue mismatch")

    damaged = copy.deepcopy(certificate)
    index = next(i for i, line in enumerate(damaged["lines"])
                 if sum(bool(d) for d in line["direction"]) == 2)
    old = damaged["lines"][index]["target"]
    new = next(entry["value"] for entry in damaged["prime_variables"]
               if entry["value"] != old)
    damaged["lines"][index]["target"] = new
    damaged["lines"][index]["residue"] = new % damaged["modulus"]
    expect("corrupt_pair_marginal", damaged, "partition identity")

    damaged = copy.deepcopy(certificate)
    varying_axis = next(axis for axis, sign in enumerate(damaged["lines"][0]["direction"])
                        if sign)
    damaged["lines"][0]["base"][varying_axis] = 1
    expect("shifted_instead_of_full_line", damaged, "hidden varying offset")
    return rejected


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    make = subparsers.add_parser("make", help="finite exact target-vector search")
    make.add_argument("n", type=int)
    make.add_argument("output", type=Path)
    make.add_argument("--modulus", type=int, default=2)
    make.add_argument("--compact", action="store_true",
                      help="store q_S and the full-family rule, not every line")
    check = subparsers.add_parser("check", help="independent certificate verification")
    check.add_argument("certificate", type=Path)
    check.add_argument("--negative-controls", action="store_true")
    subparsers.add_parser("self-test", help="finite weights, congruences, and regressions")
    args = parser.parse_args()
    if args.command == "make":
        certificate = make_certificate(args.n, args.modulus)
        if args.compact:
            del certificate["lines"]
            certificate["line_rule"] = "absolute_coordinate_set"
        result = check_certificate(certificate)
        args.output.write_text(json.dumps(certificate, indent=2) + "\n")
        print(json.dumps({"written": str(args.output), **result}, sort_keys=True))
    elif args.command == "check":
        certificate = json.loads(args.certificate.read_text())
        result = check_certificate(certificate)
        if args.negative_controls:
            result["rejected_negative_controls"] = negative_controls(certificate)
        print(json.dumps(result, sort_keys=True))
    else:
        arithmetic_controls()
        results = []
        for n in (3, 5):
            certificate = make_certificate(n)
            result = check_certificate(certificate)
            result["rejected_negative_controls"] = negative_controls(certificate)
            results.append(result)
        print(json.dumps({"arithmetic_controls": "passed", "certificates": results},
                         sort_keys=True))


if __name__ == "__main__":
    main()
