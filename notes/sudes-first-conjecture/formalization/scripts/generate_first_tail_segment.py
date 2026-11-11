#!/usr/bin/env python3
"""Generate an untrusted finite factor/Lucas certificate for a real FTT segment.

Lean checks every node and proper divisor. The generator does not establish
prime-prefix counts or the correctness of any other source data.
"""
import hashlib
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
FTT = ROOT / 'problems/prime-line-sums/inputs/cutoff2_finite_target_table_data.json'
EXPECTED_SHA256 = 'c270ec76ac4e1a00c1992fd78a3654695bd1ff94c940af773eff6687152772d8'
OUT = ROOT / 'formalizations/sude/Sude/GeneratedPrefix/FirstTailSegment.lean'


def factor(n):
    result = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            exponent = 0
            while n % d == 0:
                n //= d
                exponent += 1
            result.append((d, exponent))
        d += 1 if d == 2 else 2
    if n > 1:
        result.append((n, 1))
    return result


def witness(n, factors):
    for a in range(2, 10000):
        if pow(a, n - 1, n) == 1 and all(
            math.gcd(pow(a, (n - 1) // q, n) - 1, n) == 1 for q, _ in factors
        ):
            return a
    raise ValueError(f'no Lucas witness found for {n}')


def main():
    raw = FTT.read_bytes()
    if hashlib.sha256(raw).hexdigest() != EXPECTED_SHA256:
        raise ValueError('frozen FTT input digest mismatch')
    row = json.loads(raw)['rows'][0]
    if row[:2] != [2001, 67939607]:
        raise ValueError('unexpected first FTT row')
    start = row[1] - 106
    if start % 2 != 1:
        raise ValueError('expected an odd start')
    values = range(start, row[1] + 1, 2)
    divisors = []
    prime_values = []
    for value in values:
        factors = factor(value)
        if factors == [(value, 1)]:
            divisors.append(0)
            prime_values.append(value)
        else:
            divisors.append(factors[0][0])
    nodes = {}

    def add_node(value):
        if value in nodes:
            return
        if value == 2:
            nodes[value] = (1, [])
            return
        factors = factor(value - 1)
        for q, _ in factors:
            add_node(q)
        nodes[value] = (witness(value, factors), factors)

    for value in prime_values:
        add_node(value)
    lines = [
        'import Sude.FactorSegmentCertificate', '',
        '/-! Generated factor/Lucas evidence for the 54 odd candidates ending at',
        'the first FTT endpoint. Lean checks every certificate node and row. -/',
        'namespace Sude.GeneratedPrefix', 'set_option maxRecDepth 100000',
        'set_option maxHeartbeats 0', '',
        'def firstTailNodes : List Lucas.Node := [',
    ]
    encoded = []
    for value, (a, factors) in sorted(nodes.items()):
        fs = ', '.join(f'({q}, {e})' for q, e in factors)
        encoded.append(f'  ⟨{value}, {a}, [{fs}]⟩')
    lines += [',\n'.join(encoded), ']', '',
        'def firstTailFactors : List ℕ := [' + ', '.join(map(str, divisors)) + ']', '',
        'theorem firstTailNodes_checked : Lucas.checkCertificate firstTailNodes = true := by',
        '  decide +kernel', '',
        f'theorem firstTailFactors_checked : checkFactorRows (firstTailNodes.map Lucas.Node.value) {start} firstTailFactors = true := by',
        '  decide +kernel', '',
        'theorem firstTailSegment_exact :',
        f'    (factorSurvivors {start} firstTailFactors).toFinset =',
        f'      oddPrimeSegment {start} ( {start} + 2 * firstTailFactors.length) := by',
        f'  apply factor_certificate_segment firstTailNodes {start} firstTailFactors',
        '  · exact firstTailNodes_checked', '  · exact firstTailFactors_checked',
        '  · decide +kernel', '',
        f'theorem firstTailSegment_count : (factorSurvivors {start} firstTailFactors).length = {len(prime_values)} := by',
        '  decide +kernel', '',
        f'theorem firstTailSegment_sum : (factorSurvivors {start} firstTailFactors).sum = {sum(prime_values)} := by',
        '  decide +kernel', '',
        'theorem firstTailPrimeSegment_count_sum :',
        f'    (oddPrimeSegment {start} {row[1] + 2}).card = {len(prime_values)} ∧',
        f'    (∑ p ∈ oddPrimeSegment {start} {row[1] + 2}, p) = {sum(prime_values)} := by',
        f'  have h := factor_certificate_count_sum firstTailNodes {start} firstTailFactors',
        '    firstTailNodes_checked firstTailFactors_checked (by decide)',
        '  rw [firstTailSegment_count, firstTailSegment_sum] at h',
        f'  simpa only [show firstTailFactors.length = {len(divisors)} by decide +kernel,',
        f'    show {start} + 2 * {len(divisors)} = {row[1] + 2} by decide] using h', '',
        'end Sude.GeneratedPrefix', '',
    ]
    OUT.parent.mkdir(parents=True, exist_ok=True)
    rendered = '\n'.join(lines)
    if not OUT.exists() or OUT.read_text() != rendered:
        OUT.write_text(rendered)
    print(f'{len(divisors)} candidates, {len(prime_values)} primes, {len(nodes)} Lucas nodes, sum {sum(prime_values)}')


if __name__ == '__main__':
    main()
