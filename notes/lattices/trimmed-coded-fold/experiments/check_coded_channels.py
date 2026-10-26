#!/usr/bin/env python3
"""Exact regressions for CVP-M10's coded-channel weight/rank lemma.

This checks the explicitly constructed binary code, the local arbitrary-table
rank bound, the parity-kernel distance identity on small affine systems, and
the exact parameter schedule. It is not a formal proof or a full compiler
verification. Standard library only; no random choices are made.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from itertools import product
import json
from pathlib import Path


def polynomial_remainder(value: int, modulus: int) -> int:
    degree = modulus.bit_length() - 1
    while value and value.bit_length() - 1 >= degree:
        value ^= modulus << (value.bit_length() - 1 - degree)
    return value


def polynomial_gcd(left: int, right: int) -> int:
    while right:
        left, right = right, polynomial_remainder(left, right)
    return left


def field_multiply(left: int, right: int, modulus: int) -> int:
    result = 0
    while right:
        if right & 1:
            result ^= left
        left <<= 1
        right >>= 1
    return polynomial_remainder(result, modulus)


def field_power(value: int, exponent: int, modulus: int) -> int:
    result = 1
    while exponent:
        if exponent & 1:
            result = field_multiply(result, value, modulus)
        value = field_multiply(value, value, modulus)
        exponent >>= 1
    return result


@lru_cache(maxsize=None)
def least_irreducible(degree: int) -> int:
    """Deterministically find the first monic irreducible over F_2."""
    assert degree >= 1
    for modulus in range((1 << degree) | 1, 1 << (degree + 1), 2):
        x = polynomial_remainder(2, modulus)
        iterate = x
        good = True
        for step in range(1, degree + 1):
            iterate = field_multiply(iterate, iterate, modulus)
            if step <= degree // 2 and polynomial_gcd(iterate ^ x, modulus) != 1:
                good = False
                break
        if good and iterate == x:
            return modulus
    raise AssertionError("an irreducible must exist")


@lru_cache(maxsize=None)
def greedy_inner_rows(dimension: int) -> tuple[int, ...]:
    """Binary [8m,m,>=2m+1] map, by exact conditional expectation.

    A message v != 0 has weight w_j(v) after j rows. Candidate next row g
    is scored by sum_v 2^(j+1-w_j(v)-<g,v>). This is a common-denominator
    version of the potential in the proof. Its average over all g is
    3/2 times the previous integer score. Ties use the smallest row.
    """
    m = dimension
    assert m >= 1
    alphabet = 1 << m
    weights = [0] * alphabet
    rows: list[int] = []
    previous_score = alphabet - 1
    for step in range(8 * m):
        chosen = None
        minimum = None
        for candidate in range(alphabet):
            score = sum(
                1 << (step + 1 - weights[value] - ((value & candidate).bit_count() & 1))
                for value in range(1, alphabet)
            )
            if minimum is None or score < minimum:
                chosen, minimum = candidate, score
        assert chosen is not None and minimum is not None
        assert 2 * minimum <= 3 * previous_score
        rows.append(chosen)
        for value in range(1, alphabet):
            weights[value] += (value & chosen).bit_count() & 1
        previous_score = minimum
    assert min(weights[1:]) >= 2 * m + 1
    assert previous_score < (1 << (6 * m))
    return tuple(rows)


def inner_encode(value: int, rows: tuple[int, ...]) -> int:
    encoded = 0
    for index, row in enumerate(rows):
        encoded |= ((value & row).bit_count() & 1) << index
    return encoded


@dataclass(frozen=True)
class BinaryCode:
    dimension: int
    symbol_bits: int
    message_symbols: int
    modulus: int
    inner_rows: tuple[int, ...]
    columns: tuple[int, ...]
    elimination_basis: tuple[tuple[int, int, int], ...]

    @property
    def length(self) -> int:
        return 16 * self.message_symbols * self.symbol_bits

    @property
    def distance_lower_bound(self) -> int:
        return (self.message_symbols + 1) * (2 * self.symbol_bits + 1)

    def encode(self, source: int) -> int:
        assert 0 <= source < (1 << self.dimension)
        encoded = 0
        for index, column in enumerate(self.columns):
            if source >> index & 1:
                encoded ^= column
        return encoded

    def encode_direct(self, source: int) -> int:
        return concatenate_encode(
            source, self.symbol_bits, self.message_symbols, self.modulus, self.inner_rows
        )

    def decode(self, ambient: int) -> int:
        """A binary-linear left inverse, defined on the entire ambient space."""
        decoded = 0
        residual = ambient
        for pivot, word, preimage in self.elimination_basis:
            if residual >> pivot & 1:
                residual ^= word
                decoded ^= preimage
        return decoded

    def in_image(self, ambient: int) -> bool:
        return self.encode(self.decode(ambient)) == ambient


def concatenate_encode(source: int, m: int, k: int, modulus: int, rows: tuple[int, ...]) -> int:
    alphabet = 1 << m
    coefficients = [(source >> (j * m)) & (alphabet - 1) for j in range(k)]
    result = 0
    for point in range(2 * k):
        value = 0
        for coefficient in reversed(coefficients):
            value = field_multiply(value, point, modulus) ^ coefficient
        result |= inner_encode(value, rows) << (point * 8 * m)
    return result


@lru_cache(maxsize=None)
def construct_code(dimension: int) -> BinaryCode:
    assert dimension >= 1
    m = (2 * dimension - 1).bit_length()
    k = (dimension + m - 1) // m
    assert 1 <= m <= dimension
    assert 2 * k <= 1 << m
    modulus = least_irreducible(m)
    rows = greedy_inner_rows(m)
    columns = tuple(
        concatenate_encode(1 << index, m, k, modulus, rows)
        for index in range(dimension)
    )
    basis: dict[int, tuple[int, int]] = {}
    for index, column in enumerate(columns):
        residual, preimage = column, 1 << index
        while residual:
            pivot = residual.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = residual, preimage
                break
            word, word_preimage = basis[pivot]
            residual ^= word
            preimage ^= word_preimage
        assert residual, "the concatenated encoder must be injective"
    ordered_basis = tuple((pivot, *basis[pivot]) for pivot in sorted(basis, reverse=True))
    code = BinaryCode(dimension, m, k, modulus, rows, columns, ordered_basis)
    assert code.length <= 32 * dimension
    assert 8 * code.distance_lower_bound > code.length
    assert all(code.decode(column) == (1 << index) for index, column in enumerate(columns))
    return code


def field_rank(matrix: list[list[int]], modulus: int) -> int:
    if not matrix:
        return 0
    work = [row[:] for row in matrix]
    rows, columns = len(work), len(work[0])
    alphabet = 1 << (modulus.bit_length() - 1)
    rank = 0
    for column in range(columns):
        pivot = next((row for row in range(rank, rows) if work[row][column]), None)
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        inverse = field_power(work[rank][column], alphabet - 2, modulus)
        work[rank] = [field_multiply(value, inverse, modulus) for value in work[rank]]
        for row in range(rank + 1, rows):
            scalar = work[row][column]
            if scalar:
                work[row] = [
                    value ^ field_multiply(scalar, pivot_value, modulus)
                    for value, pivot_value in zip(work[row], work[rank])
                ]
        rank += 1
        if rank == rows:
            break
    return rank


def check_inner_codes() -> list[dict]:
    results = []
    for m in range(1, 7):
        rows = greedy_inner_rows(m)
        weights = [inner_encode(value, rows).bit_count() for value in range(1, 1 << m)]
        potential = sum((Fraction(2) ** (2 * m - weight) for weight in weights), Fraction(0))
        upper_bound = (2 ** m - 1) * Fraction(2) ** (2 * m) * Fraction(3, 4) ** (8 * m)
        assert potential <= upper_bound < 1
        assert min(weights) >= 2 * m + 1
        results.append({
            "m": m,
            "length": 8 * m,
            "minimum_weight": min(weights),
            "distance_lower_bound": 2 * m + 1,
            "nonzero_messages_checked": len(weights),
            "potential": str(potential),
            "rows": list(rows),
        })
    return results


def check_concatenated_codes() -> dict:
    results = []
    linearity_pairs = 0
    checked_words = 0
    for dimension in range(1, 13):
        code = construct_code(dimension)
        words = [code.encode(source) for source in range(1 << dimension)]
        assert len(set(words)) == len(words)
        for source, encoded in enumerate(words):
            assert encoded == code.encode_direct(source)
            assert code.decode(encoded) == source
            assert code.in_image(encoded)
        if dimension <= 5:
            for left in range(1 << dimension):
                for right in range(1 << dimension):
                    assert words[left] ^ words[right] == words[left ^ right]
                    linearity_pairs += 1
        minimum_weight = min(word.bit_count() for word in words[1:])
        assert minimum_weight >= code.distance_lower_bound
        assert code.length <= 32 * dimension
        assert 8 * minimum_weight > code.length
        checked_words += len(words)
        results.append({
            "C": dimension,
            "m": code.symbol_bits,
            "k": code.message_symbols,
            "length": code.length,
            "minimum_weight": minimum_weight,
            "distance_lower_bound": code.distance_lower_bound,
            "messages_checked": len(words),
            "field_modulus": code.modulus,
        })

    smallest = construct_code(1)
    image_count = 0
    for ambient in range(1 << smallest.length):
        image_count += smallest.in_image(ambient)
    assert image_count == 2

    # Decoder linearity and the exact w=ERw membership criterion away from
    # the code image. Enumerating all two-bit ambient perturbations is small.
    decoder_pairs = 0
    for dimension in range(1, 7):
        code = construct_code(dimension)
        for i in range(code.length):
            for j in range(code.length):
                left, right = 1 << i, 1 << j
                assert code.decode(left ^ right) == code.decode(left) ^ code.decode(right)
                assert not code.in_image(left), "distance exceeds one"
                decoder_pairs += 1
    return {
        "cases": results,
        "messages_checked": checked_words,
        "linearity_pairs_checked": linearity_pairs,
        "ambient_membership_words_checked": 1 << smallest.length,
        "decoder_linearity_pairs_checked": decoder_pairs,
    }


def check_local_rank_bound() -> dict:
    cases = []
    total = 0
    for field_bits, channels in ((1, 3), (2, 2), (2, 3)):
        alphabet = 1 << field_bits
        modulus = least_irreducible(field_bits)
        code = construct_code(channels)
        encoded_weights = [code.encode(message).bit_count() for message in range(1 << channels)]
        rank_histogram: dict[int, int] = {}
        checked = 0
        for table in product(range(1 << channels), repeat=alphabet):
            # Two row powers and q+1 column powers. Whole channel vectors
            # share a tuple u, exactly as in the vector-valued construction.
            matrix = [[0] * (alphabet + 1) for _ in range(2 * channels)]
            for point, channel_vector in enumerate(table):
                for a in range(2):
                    for channel in range(channels):
                        if channel_vector >> channel & 1:
                            for b in range(alphabet + 1):
                                matrix[a * channels + channel][b] ^= field_power(point, a + b, modulus)
            rank = field_rank(matrix, modulus)
            active = sum(vector != 0 for vector in table)
            weight = sum(encoded_weights[vector] for vector in table)
            assert rank <= active
            assert weight >= code.distance_lower_bound * active
            assert weight >= code.distance_lower_bound * rank
            rank_histogram[rank] = rank_histogram.get(rank, 0) + 1
            checked += 1
        total += checked
        cases.append({
            "field_size": alphabet,
            "channels": channels,
            "tables_checked": checked,
            "rank_histogram": rank_histogram,
        })
    return {"cases": cases, "tables_checked": total}


def check_parity_kernel() -> dict:
    """Enumerate every 2x3 binary affine system and signed residual [-2,2]^3."""
    systems = 0
    consistent = 0
    integer_residuals = list(product(range(-2, 3), repeat=3))
    for row0 in range(8):
        for row1 in range(8):
            for rhs in range(4):
                binary_minimum = None
                integer_minimum = None
                for word in range(8):
                    syndrome = ((word & row0).bit_count() & 1) | (((word & row1).bit_count() & 1) << 1)
                    if syndrome == rhs:
                        weight = word.bit_count()
                        binary_minimum = weight if binary_minimum is None else min(binary_minimum, weight)
                for residual in integer_residuals:
                    parity = sum((value & 1) << index for index, value in enumerate(residual))
                    syndrome = ((parity & row0).bit_count() & 1) | (((parity & row1).bit_count() & 1) << 1)
                    if syndrome == rhs:
                        squared_norm = sum(value * value for value in residual)
                        assert squared_norm >= parity.bit_count()
                        integer_minimum = squared_norm if integer_minimum is None else min(integer_minimum, squared_norm)
                assert integer_minimum == binary_minimum
                systems += 1
                consistent += binary_minimum is not None
    return {
        "affine_systems_checked": systems,
        "consistent_systems": consistent,
        "signed_residual_checks": systems * len(integer_residuals),
        "integer_coordinate_range": [-2, 2],
    }


def schedule(epsilon: Fraction) -> dict:
    assert 0 < epsilon < Fraction(1, 2)
    h = 2
    while h < 1 + 4 / epsilon:
        h *= 2
    threshold = h / epsilon - 2 * h
    r = threshold.numerator // threshold.denominator + 1
    p0 = Fraction(r + 2 * h, h - 1)
    c0 = Fraction(r, 2 * (r + 2 * h))
    assert r >= 1
    assert c0 > Fraction(1, 2) - epsilon
    assert (Fraction(1, 2) - c0) * p0 == Fraction(h, h - 1)
    assert p0 <= 1 / epsilon + Fraction(1, 4) + epsilon / 4
    assert p0 < 1 / epsilon + Fraction(3, 8)
    assert p0 < 1 / epsilon + 1
    return {
        "epsilon": str(epsilon),
        "h": h,
        "r": r,
        "p0": str(p0),
        "c0": str(c0),
        "deficit_times_p0": str(Fraction(h, h - 1)),
        "clean_rank_degree": str(1 / epsilon + 1),
        "r_less_than_h": r < h,
    }


def check_schedules() -> dict:
    sample_epsilons = [
        Fraction(1, 1000), Fraction(1, 100), Fraction(1, 10), Fraction(1, 4),
        Fraction(1, 3), Fraction(2, 5), Fraction(49, 100), Fraction(499, 1000),
        Fraction(4999, 10000), Fraction(499999, 1000000),
    ]
    all_epsilons = set(sample_epsilons)
    all_epsilons.update(
        Fraction(numerator, denominator)
        for denominator in range(3, 41)
        for numerator in range(1, (denominator + 1) // 2)
    )
    all_epsilons.update(Fraction(1, 2) - Fraction(1, 2 ** exponent) for exponent in range(2, 21))
    rows = [schedule(epsilon) for epsilon in sorted(all_epsilons)]

    # The actual radix degree estimate remains valid when r<h, including r=1.
    radix_cases = 0
    for r in range(1, 7):
        for s in (2, 4, 8):
            top_degree_bound = r * (s - 1) + (r - 1) * (s - 1) + 4 * s
            assert top_degree_bound < (2 * r + 4) * s
            radix_cases += 1
    return {
        "schedules_checked": len(rows),
        "r_less_than_h_cases": sum(row["r_less_than_h"] for row in rows),
        "radix_degree_cases": radix_cases,
        "sample_schedules": [schedule(epsilon) for epsilon in sample_epsilons],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="write the exact JSON certificate")
    args = parser.parse_args()
    certificate = {
        "schema": "cvp.coded-channels.v1",
        "lane": "CVP-M10",
        "scope": "Exact component regressions; not a full reduction test or formal verification.",
        "checker_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "inner_codes": check_inner_codes(),
        "concatenated_codes": check_concatenated_codes(),
        "local_rank_bound": check_local_rank_bound(),
        "parity_kernel": check_parity_kernel(),
        "parameter_schedule": check_schedules(),
    }
    rendered = json.dumps(certificate, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered)
    print("PASS: cvp.coded-channels.v1")
    print(sha256(rendered.encode()).hexdigest())
    print(json.dumps({
        "code_messages": certificate["concatenated_codes"]["messages_checked"],
        "local_tables": certificate["local_rank_bound"]["tables_checked"],
        "signed_residual_checks": certificate["parity_kernel"]["signed_residual_checks"],
        "schedules": certificate["parameter_schedule"]["schedules_checked"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
