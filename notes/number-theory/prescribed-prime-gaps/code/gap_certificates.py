#!/usr/bin/env python3
"""Generate and independently verify exact consecutive-prime-gap witnesses.

Only standard-library integer arithmetic is used. Verification uses trial
division, not Miller--Rabin, floating point, or the generator's sieve.
"""
from __future__ import annotations

import argparse
import json
from math import isqrt
from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def trial_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, isqrt(n) + 1, 2))


def proper_factor(n: int) -> int:
    if n % 2 == 0 and n > 2:
        return 2
    for d in range(3, isqrt(n) + 1, 2):
        if n % d == 0:
            return d
    raise ValueError(f'No proper factor of {n}; interval is not certified')


def generate(max_gap: int, limit: int) -> dict:
    require(max_gap >= 2 and max_gap % 2 == 0, 'max_gap must be positive and even')
    sieve = bytearray(b'\x01') * (limit + 1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start::p] = b'\x00' * ((limit - start) // p + 1)
    found: dict[int, tuple[int, int]] = {}
    previous = 2
    index = 1
    for n in range(3, limit + 1, 2):
        if not sieve[n]:
            continue
        gap = n - previous
        if gap % 2 == 0 and gap <= max_gap and gap not in found:
            found[gap] = (previous, index)
        previous = n
        index += 1
        if len(found) == max_gap // 2:
            break
    require(len(found) == max_gap // 2,
            f'missing gaps: {[g for g in range(2,max_gap+1,2) if g not in found]}')
    witnesses = []
    for gap, (p, prime_index) in sorted(found.items()):
        witnesses.append({'gap': gap, 'left': p, 'right': p + gap,
                          'generator_first_index': prime_index,
                          'interior_factors': [proper_factor(p+j) for j in range(1,gap)]})
    return {'format': 'exact-prime-gap-witnesses-v1', 'max_gap': max_gap,
            'generator_search_limit': limit,
            'index_status': 'generator metadata; verifier certifies occurrences, not minimality or indices',
            'witnesses': witnesses}


def verify(data: dict) -> dict:
    require(data.get('format') == 'exact-prime-gap-witnesses-v1', 'unknown format')
    max_gap = data['max_gap']
    require(type(max_gap) is int and max_gap >= 2 and max_gap % 2 == 0, 'bad max_gap')
    records = data['witnesses']
    require(len(records) == max_gap // 2, 'wrong record count')
    seen = set()
    checks = 0
    maximum = 0
    for record in records:
        g, p, q = record['gap'], record['left'], record['right']
        require(all(type(v) is int for v in [g,p,q]), 'noninteger data')
        require(2 <= g <= max_gap and g % 2 == 0 and g not in seen, 'bad/duplicate gap')
        require(q - p == g, 'wrong difference')
        require(trial_prime(p) and trial_prime(q), 'endpoint not prime')
        factors = record['interior_factors']
        require(len(factors) == g-1, 'wrong factor count')
        for j, divisor in enumerate(factors, 1):
            n = p+j
            require(type(divisor) is int and 1 < divisor < n and n % divisor == 0,
                    f'invalid proper factor at gap {g}, offset {j}')
            checks += 1
        seen.add(g)
        maximum = max(maximum, q)
    require(seen == set(range(2,max_gap+1,2)), 'coverage mismatch')
    return {'certified_even_gaps':len(seen), 'range':[2,max_gap],
            'endpoint_primality_proofs':2*len(seen),
            'proper_divisor_certificates':checks,'largest_endpoint':maximum,
            'method':'exact trial division and integer divisibility'}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    gen = sub.add_parser('generate')
    gen.add_argument('path', type=Path)
    gen.add_argument('--max-gap', type=int, default=180)
    gen.add_argument('--limit', type=int, default=100_000_000)
    check = sub.add_parser('verify')
    check.add_argument('path', type=Path)
    args = parser.parse_args()
    if args.command == 'generate':
        data = generate(args.max_gap,args.limit)
        args.path.parent.mkdir(parents=True, exist_ok=True)
        args.path.write_text(json.dumps(data, indent=2)+'\n')
    else:
        data = json.loads(args.path.read_text())
    print(json.dumps(verify(data), sort_keys=True))


if __name__ == '__main__':
    main()
