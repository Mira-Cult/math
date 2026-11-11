#!/usr/bin/env python3
"""Exact finite power-of-two prime-pair populations; no square cutoff claim.

This standalone Python checker imports no producer arithmetic module and needs
no prime table, compiled program, third-party package, or discovery artifact.
"""
from array import array
from bisect import bisect_left, bisect_right
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, permutations
from math import isqrt
from pathlib import Path
import copy
import hashlib
import json
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
SELF = 'code/cutoff2_finite_prefix_population.py'
INPUT = 'inputs/cutoff2_finite_prefix_population_inputs.json'
SOURCES = {
    'PROBLEM.md': '9632c547445ed661a5df4ccfdc14892a0aeaf3ed108203c08bf075df8720c023',
    'manuscripts/cutoff2_prefix_balance_experiment.md': 'efca80ca4c0c5b470cd46e90b736e54143b1337b7aadf2593f820570e626f395',
    'manuscripts/cutoff2_finite_prefix_population.md': '468c71cd24241422fe6cf6e38ce2f61e0a1d5179dbd4e72fc2c667d42527eba4',
}
SCHEMA = 'sude-finite-prefix-populations-v1'
SCOPE = ('Finite disjoint common-gap prefix populations on every integer order '
         '2400 through 3000, with conditional balanced allocation; no square '
         'cutoff, analytic mean bound, or formal proof is asserted.')
PARAMETERS = {
    'sieve_bound': 95000000, 'degree': 6, 'order_min': 2400,
    'order_max': 3000, 'pairs_per_stage': 18048, 'stage_count': 24,
    'gaps': [1 << j for j in range(1, 25)],
    'screened_odd_prime_count': 13, 'screened_prime_floor': 43,
    'profiles': [
        {'name': 'U', 'lower': 44, 'upper': 95000000},
        {'name': 'C27', 'lower': 27000000, 'upper': 74000000},
        {'name': 'C40', 'lower': 40000000, 'upper': 88000000},
    ],
}
EXPECTED = {
    'prime_count': 5489749, 'coverage': 33554430, 'max_entries': 866304,
    'U': {'sum_range_squares': 414426016843200, 'max_range': 4912776,
          'variance': 7556209775282304, 'allocation_upper': 195208873,
          'retained_stream_sha256': '1abf1278086342d2e32d714569c83004fc15556e9151b9a3d5972f61341b9cc1'},
    'C27': {'sum_range_squares': 765704561939244, 'max_range': 8636928,
            'variance': 14081068216015128, 'allocation_upper': 266480449,
            'retained_stream_sha256': '54c52fb6a252937c1a6be65f7309c316f95cbf00f65274044e7de397fdb801a5'},
    'C40': {'sum_range_squares': 801615658790268, 'max_range': 8615460,
            'variance': 14725986462271224, 'allocation_upper': 272514584,
            'retained_stream_sha256': 'caec7af9f481ee00d0b7b5014c2f756c373b9e8b2a11022ee8c70f57affb9d0e'},
}
COUNTS = Counter()


def require(condition, label, category='arithmetic'):
    COUNTS[category] += 1
    if not condition:
        raise ValueError(label)


def exact_equal(left, right):
    if type(left) is not type(right):
        return False
    if isinstance(left, dict):
        return left.keys() == right.keys() and all(exact_equal(left[k], right[k]) for k in left)
    if isinstance(left, list):
        return len(left) == len(right) and all(exact_equal(a, b) for a, b in zip(left, right))
    return left == right


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def parse_json(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'duplicate JSON key', 'input')
            result[key] = value
        return result
    def bad(value):
        raise ValueError('nonfinite JSON literal '+value)
    return json.loads(raw, object_pairs_hook=pairs, parse_constant=bad)


def regular_bytes(path):
    require(not path.is_symlink() and path.is_file(), 'regular non-symlink file', 'source')
    require(all(not ancestor.is_symlink() for ancestor in path.parents),
            'non-symlink file ancestors', 'source')
    raw = path.read_bytes()
    require(bool(raw), 'nonempty file', 'source')
    return raw


def source_check(bindings, root=ROOT):
    needed = set(SOURCES) | {SELF}
    require(bool(SOURCES) and type(bindings) is dict and set(bindings) == needed,
            'complete exact nonempty required source map', 'source')
    for name in sorted(needed):
        value = bindings[name]
        require(type(value) is str and len(value) == 64
                and all(c in '0123456789abcdef' for c in value),
                'canonical lowercase SHA-256', 'source')
        if name != SELF:
            require(value == SOURCES[name], 'fixed required source digest', 'source')
        require(digest(regular_bytes(root/name)) == value, 'source bytes match digest', 'source')


def trial_prime(n):
    return type(n) is int and n >= 2 and all(n % k for k in range(2, isqrt(n)+1))


def odd_sieve(bound):
    require(type(bound) is int and 100 <= bound <= 200000000, 'finite odd-sieve domain')
    mask = bytearray(b'\x01')*((bound+1)//2)
    mask[0] = 0
    for p in range(3, isqrt(bound)+1, 2):
        if mask[p//2]:
            start = p*p//2
            mask[start::p] = b'\x00'*((len(mask)-1-start)//p+1)
    return mask


def prime_at(mask, n):
    return n == 2 or (n >= 3 and n % 2 == 1 and n//2 < len(mask) and bool(mask[n//2]))


def little_endian(values):
    data = array('I', values)
    require(data.itemsize == 4, 'four-byte unsigned integer array')
    if sys.byteorder != 'little':
        data.byteswap()
    return data.tobytes()


def choose_window(values, size):
    require(type(size) is int and size > 0 and len(values) >= size,
            'positive feasible retained window')
    require(all(type(x) is int and x >= 0 for x in values)
            and all(a < b for a, b in zip(values, values[1:])),
            'strictly increasing integer candidate labels')
    width, first = min((values[i+size-1]-values[i], i)
                       for i in range(len(values)-size+1))
    return first, width


def gap_check(gap):
    require(type(gap) is int and gap >= 2 and gap & (gap-1) == 0,
            'positive even power-of-two gap')
    require(gap % 3 != 0, 'gap is coprime to three')


def select_stage(mask, primes, lower, upper, gap, size, stage):
    gap_check(gap)
    require(all(type(x) is int for x in (lower, upper, size, stage))
            and 44 <= lower <= upper <= 2*len(mask),
            'exact screened finite stage domain')
    start = bisect_left(primes, lower)
    stop = bisect_right(primes, upper-gap)
    half = gap//2
    candidates = array('I', (p for p in primes[start:stop]
                            if mask[p//2] and mask[p//2+half]))
    first, width = choose_window(candidates, size)
    kept = candidates[first:first+size]
    before = mask.count(1)
    for p in kept:
        require(lower <= p < p+gap <= upper and p > 43,
                'both selected endpoints inside screened interval', 'selection')
        require(mask[p//2] == mask[(p+gap)//2] == 1,
                'prime endpoints distinct from every earlier retained entry', 'selection')
        mask[p//2] = mask[(p+gap)//2] = 0
    require(mask.count(1) == before-2*size, 'only retained endpoints deleted', 'selection')
    row = {
        'stage': stage, 'gap': gap, 'candidates': len(candidates),
        'chosen_start': first, 'first_lower': kept[0], 'last_lower': kept[-1],
        'range': width, 'sum_lower': sum(kept), 'min_upper': kept[0]+gap,
        'max_upper': kept[-1]+gap, 'retained_pairs': size,
        'candidate_sha256': digest(little_endian(candidates)),
        'retained_sha256': digest(little_endian(kept)),
    }
    return kept, row


def log_bounds(value, terms=32):
    value, power = F(value), 0
    require(value > 0 and type(terms) is int and terms >= 1, 'logarithm domain')
    while value > 2:
        value /= 2
        power += 1
    while value < 1:
        value *= 2
        power -= 1
    def local(x):
        z = (x-1)/(x+1)
        lo = 2*sum((z**(2*j+1)/F(2*j+1) for j in range(terms)), F())
        hi = lo+2*z**(2*terms+1)/(F(2*terms+1)*(1-z*z))
        return lo, hi
    lo, hi = local(value)
    a, b = local(F(2))
    return (lo+power*a, hi+power*b) if power >= 0 else (lo+power*b, hi+power*a)


def sqrt_upper(value):
    value = F(value)
    require(value >= 0, 'nonnegative squared bound')
    result = isqrt(value.numerator//value.denominator)
    if result*result < value:
        result += 1
    require(result*result >= value and (result == 0 or (result-1)**2 < value),
            'exact least integer square-root majorant')
    return result


def complete_grid(gaps, multiplicity=1):
    require(type(multiplicity) is int and multiplicity >= 1, 'positive grid multiplicity')
    coverage = 0
    for gap in gaps:
        gap_check(gap)
        for _ in range(multiplicity):
            require(gap <= coverage+2, 'complete even-grid extension')
            coverage += gap
    return coverage


def order_table(kept, degree, order_min, order_max):
    require(type(degree) is int and degree >= 2 and degree % 2 == 0,
            'positive even slot degree')
    prefix_sums = []
    for seq in kept:
        row = [0]
        for p in seq:
            row.append(row[-1]+p)
        prefix_sums.append(row)
    gaps = PARAMETERS['gaps'][:len(kept)]
    coverage = complete_grid(gaps)
    previous_ranges = [0]*len(kept)
    previous_variance = 0
    rows = []
    for n in range(order_min, order_max+1):
        q = degree*(n+8)
        require(all(q <= len(seq) for seq in kept), 'all-order truncation within every population')
        ranges = [seq[q-1]-seq[0] for seq in kept]
        require(all(a <= b for a, b in zip(previous_ranges, ranges)),
                'range monotonicity across integer Q jumps')
        variance = 3*degree*sum(w*w for w in ranges)+4*max(ranges)**2
        require(variance >= previous_variance, 'all-order variance monotonicity')
        s = sum(row[q] for row in prefix_sums)
        mu = F(s, q)+F(coverage, 2)
        lo_mu = min(F(row[q], q)+F(g, 2) for row, g in zip(prefix_sums, gaps))
        hi_mu = max(F(row[q], q)+F(g, 2) for row, g in zip(prefix_sums, gaps))
        total = 2*s+q*coverage
        require(2*q*mu == total, 'actual selected-mean identity at every order')
        rows.append({'n': n, 'pairs_per_stage': q, 'reserved_entries': 2*q*len(kept),
                     'variance': variance, 'max_range': max(ranges),
                     'sum_lower': s, 'prefix_prime_sum': total,
                     'sum_stage_means': str(mu), 'min_stage_mean': str(lo_mu),
                     'max_stage_mean': str(hi_mu),
                     'min_midpoint': min(seq[0]+g//2 for seq, g in zip(kept, gaps)),
                     'max_midpoint': max(seq[q-1]+g//2 for seq, g in zip(kept, gaps))})
        previous_ranges, previous_variance = ranges, variance
    return rows


def protected_interval_count(kept, gaps, q, left, right, closed_left=False, closed_right=True):
    """Exact invoice on verified ordered populations, with rational endpoints."""
    require(type(q) is int and q > 0 and len(kept) == len(gaps)
            and all(q <= len(seq) for seq in kept), 'protected interval cardinalities')
    require(type(left) in (int, F) and type(right) in (int, F) and left <= right
            and type(closed_left) is bool and type(closed_right) is bool,
            'exact rational interval and endpoint conventions')
    count = 0
    for seq, gap in zip(kept, gaps):
        for shift in (0, gap):
            lo, hi = left-shift, right-shift
            first = (bisect_left if closed_left else bisect_right)(seq, lo, 0, q)
            last = (bisect_right if closed_right else bisect_left)(seq, hi, 0, q)
            count += max(0, last-first)
    return count


def interval_controls():
    kept, gaps = [[59, 71], [101, 107], [127, 163]], [2, 2, 4]
    endpoints = [43, 59, 60, 61, 73, F(201, 2), 107, 131, 167, 200]
    checks = 0
    for q in (1, 2):
        entries = [p+shift for seq, gap in zip(kept, gaps) for p in seq[:q] for shift in (0, gap)]
        for left in endpoints:
            for right in endpoints:
                if right < left:
                    continue
                for cl, cr in ((False, False), (False, True), (True, False), (True, True)):
                    expected = sum((x >= left if cl else x > left) and
                                   (x <= right if cr else x < right) for x in entries)
                    got = protected_interval_count(kept, gaps, q, left, right, cl, cr)
                    require(got == expected, 'exact protected window invoice with every endpoint convention', 'mechanism')
                    checks += 1
    return checks


def enumerate_profile(base, primes, profile):
    live = bytearray(base)
    for p in range(1, 44, 2):
        live[p//2] = 0
    available = live.count(1)
    kept, stages = [], []
    stream = hashlib.sha256()
    for stage, gap in enumerate(PARAMETERS['gaps']):
        seq, row = select_stage(live, primes, profile['lower'], profile['upper'],
                                gap, PARAMETERS['pairs_per_stage'], stage)
        kept.append(seq)
        stages.append(row)
        stream.update(little_endian(seq))
    widths = [row['range'] for row in stages]
    sum_squares = sum(w*w for w in widths)
    variance = 3*PARAMETERS['degree']*sum_squares+4*max(widths)**2
    orders = order_table(kept, PARAMETERS['degree'], PARAMETERS['order_min'], PARAMETERS['order_max'])
    upper = sqrt_upper(F(variance)*log_bounds(8*PARAMETERS['order_max']+8)[1]/2)
    summary = {'name': profile['name'], 'lower': profile['lower'], 'upper': profile['upper'],
               'available_initial': available, 'available_final': live.count(1),
               'reserved_entries': 2*PARAMETERS['pairs_per_stage']*len(kept),
               'sum_range_squares': sum_squares, 'max_range': max(widths),
               'variance': variance, 'allocation_upper': upper,
               'retained_stream_sha256': stream.hexdigest(),
               'final_live_mask_sha256': digest(live),
               'order_table_sha256': digest(canonical(orders)), 'stages': stages}
    require(available-summary['available_final'] == summary['reserved_entries'],
            'exact full-profile deletion accounting')
    return summary, kept, orders


def verify_profile(got, expected):
    require(exact_equal(got, expected), 'complete exact stage and profile certificate')
    fixed = EXPECTED[got['name']]
    require(all(exact_equal(got[k], v) for k, v in fixed.items()), 'fixed published profile arithmetic')
    require(got['reserved_entries'] == EXPECTED['max_entries'], 'fixed exact total reservation')


def window_controls():
    checked = 0
    for length in range(3, 7):
        for values in combinations(range(9), length):
            for size in range(1, length+1):
                first, width = choose_window(values, size)
                best = min(max(s)-min(s) for s in combinations(values, size))
                require(width == best and all(values[i+size-1]-values[i] > width for i in range(first)),
                        'exhaustive subset optimum and leftmost tie', 'mechanism')
                checked += 1
    return checked


def sieve_controls():
    checks = 0
    for bound in (100, 121, 343, 503, 1001, 5003, 20011):
        mask = odd_sieve(bound)
        for p in range(bound+1):
            require(prime_at(mask, p) == trial_prime(p), 'independent full trial-division sieve comparison', 'mechanism')
            checks += 1
        for gap in (2, 4, 8, 16, 32, 64):
            edges = [(p, p+gap) for p in range(45, bound-gap+1, 2)
                     if prime_at(mask, p) and prime_at(mask, p+gap)]
            entries = [p for pair in edges for p in pair]
            require(len(entries) == len(set(entries)), 'every coprime-three gap edge already disjoint', 'mechanism')
            checks += 1
    return checks


def permutation_controls():
    cases = increments = 0
    for size in range(3, 7):
        weights = [2, 1]+[1]*(size-3)+[0]
        values = [F(j*j+1, 3) for j in range(size)]
        total = F()
        for order in permutations(values):
            assigned = F()
            left = list(order)
            for i, w in enumerate(weights[:-1]):
                rest = sum(weights[i+1:])
                before = assigned+F(w+rest, len(left))*sum(left)
                value = left.pop(0)
                after = assigned+w*value+F(rest, len(left))*sum(left)
                coefficient = w-F(rest, len(left))
                old_mean = (sum(left)+value)/(len(left)+1)
                require(after-before == coefficient*(value-old_mean) and 0 <= coefficient <= w,
                        'weighted permutation conditional increment and range', 'mechanism')
                assigned += w*value
                increments += 1
            total += assigned
            cases += 1
        factorial = 1
        for j in range(2, size+1):
            factorial *= j
        require(total/factorial == F(sum(weights), size)*sum(values),
                'exact allocation expectation', 'mechanism')
    return {'permutations': cases, 'conditional_increments': increments}


def cancellation_controls():
    checks = 0
    for n in (31, 101, 2500, 3000):
        for degree in (2, 4, 6):
            for stages in (1, 2):
                r = 2*degree*stages
                for other in (0, 3, 7):
                    N = n*n-r*(n+8)-other
                    if N <= 0:
                        continue
                    for q in (0, 1, 2, 3):
                        A = F(17, 5)-stages*F(11, 7)
                        left = 2*degree*A-F((n-r-q)*2*degree*(n+8), N)*A
                        right = F(2*degree, N)*A*((n+8)*q-other-8*n)
                        require(left == right, 'exact prefix and unused-pool mean cancellation', 'mechanism')
                        checks += 1
    require(F(119, 750)*165000000 < 27000000,
            'conditional low wide window avoids both central profiles')
    require(F(613, 750)*97000000 > 74000000,
            'conditional high wide window avoids C27')
    require(F(613, 750)*108000000 > 88000000,
            'conditional high wide window avoids C40 with stronger X floor')
    return checks


def pair_control(rows, gaps, size, expected_sum=None):
    require(type(rows) is list and len(rows) == len(gaps), 'complete finite stage list', 'mechanism')
    seen = set()
    total = 0
    for row, gap in zip(rows, gaps):
        gap_check(gap)
        require(type(row) is list and len(row) == size, 'exact fixture stage cardinality', 'mechanism')
        for pair in row:
            require(type(pair) is tuple and len(pair) == 2 and all(type(x) is int for x in pair),
                    'integer labelled pair', 'mechanism')
            a, b = pair
            require(a > 43 and b-a == gap and trial_prime(a) and trial_prime(b),
                    'independent fixture primality and common stage gap', 'mechanism')
            require(a not in seen and b not in seen, 'no fixture prime reused', 'mechanism')
            seen.update((a, b))
            total += a+b
    if expected_sum is not None:
        require(type(expected_sum) is int and total == expected_sum,
                'actual retained sum, not candidate or previous mean', 'mechanism')
    return total


def balanced_fixture(n=257, degree=2, stages=5):
    """Finite support test, not an expander theorem or complete prime square."""
    require(n % 2 == 1 and degree % 2 == 0 and n > 16*degree*stages,
            'PB support fixture domain')
    base = odd_sieve(750000)
    require(base.count(1) < n*n, 'every fixture prime lies in prescribed odd pool')
    primes = array('I', (2*i+1 for i, flag in enumerate(base) if flag and 2*i+1 > 43))
    live = bytearray(base)
    for p in range(1, 44, 2):
        live[p//2] = 0
    lists = []
    Q = degree*(n+8)
    for stage, gap in enumerate(PARAMETERS['gaps'][:stages]):
        seq, _ = select_stage(live, primes, 44, 750000, gap, Q, stage)
        lists.append(seq)
    occupied, slots = set(), []
    stage_slots = [[] for _ in range(stages)]
    used_rows, used_columns = set(), set()
    ordinary = {'rows': [0]*n, 'columns': [0]*n}

    def add(cells, stage, kind, reservoir):
        require(len(cells) == 2 and cells[0] != cells[1] and not occupied.intersection(cells),
                'fixture cells distinct across all pairs and stages', 'mechanism')
        occupied.update(cells)
        pair_id = len(slots)
        slots.append({'cells': cells, 'stage': stage, 'kind': kind, 'reservoir': reservoir})
        stage_slots[stage].append(pair_id)
        if kind == 'ordinary':
            for r, c in cells:
                require(r != c and r+c != n-1, 'ordinary fixture avoids both diagonals', 'mechanism')
                ordinary['rows'][r] += 1
                ordinary['columns'][c] += 1

    for stage in range(stages):
        for diagonal in (0, 1):
            f = (lambda i: i) if diagonal == 0 else (lambda i: n-1-i)
            other = lambda i: n-1-f(i)
            for copy_id in range(2*degree):
                i = next(i for i in range(n) if i not in used_rows
                         and f(i) not in used_columns and i != n//2)
                j = next(j for j in range(n) if j not in used_rows and j not in (i, n-1-i))
                c = f(i)
                k = next(k for k in range(n) if k not in used_columns
                         and k not in {f(i), f(j), other(i), other(j)})
                add([(i, c), (i, k)], stage, 'rectangle', ('diagonal', diagonal, copy_id))
                add([(j, c), (j, k)], stage, 'rectangle', ('partner', diagonal, copy_id))
                used_rows.update((i, j))
                used_columns.update((c, k))

    for stage in range(stages):
        for transpose in (False, True):
            for layer in range(degree//2):
                pi = [(i+1+layer+int(transpose)*(degree//2)) % n for i in range(n)]
                choices, right_degrees = [], [0]*n
                for i in range(n):
                    allowed = []
                    for offset in range(n):
                        c = (i+offset) % n
                        cells = [(c, i), (c, pi[i])] if transpose else [(i, c), (pi[i], c)]
                        if all(cell not in occupied and cell[0] != cell[1]
                               and sum(cell) != n-1 for cell in cells):
                            allowed.append(c)
                            right_degrees[c] += 1
                    require(len(allowed) > n//2, 'fixture allowed left degree', 'mechanism')
                    choices.append(allowed)
                require(min(right_degrees) > n//2, 'fixture allowed right degree', 'mechanism')
                owners = [-1]*n
                def augment(i, seen):
                    for c in choices[i]:
                        if c in seen:
                            continue
                        seen.add(c)
                        if owners[c] < 0 or augment(owners[c], seen):
                            owners[c] = i
                            return True
                    return False
                for i in range(n):
                    require(augment(i, set()), 'fixture perfect matching', 'mechanism')
                columns = {i: c for c, i in enumerate(owners)}
                for i in range(n):
                    c = columns[i]
                    cells = [(c, i), (c, pi[i])] if transpose else [(i, c), (pi[i], c)]
                    add(cells, stage, 'ordinary', (transpose, layer, i))
    require(all(x == 2*degree*stages for values in ordinary.values() for x in values),
            'ordinary support has equal main cell counts', 'mechanism')
    require(all(len(row) == Q for row in stage_slots), 'all labelled stage slots filled', 'mechanism')
    entries, weights = set(), [Counter() for _ in range(2*n+2)]
    reservoirs = {}
    for stage, pair_ids in enumerate(stage_slots):
        gap = PARAMETERS['gaps'][stage]
        for index, pair_id in enumerate(pair_ids):
            p = lists[stage][index]
            require(p not in entries and p+gap not in entries, 'all assigned fixture entries distinct', 'mechanism')
            entries.update((p, p+gap))
            slot = slots[pair_id]
            key = slot['reservoir']
            if key[0] != 'partner':
                if key[0] == 'diagonal':
                    key = ('diagonal', key[1])
                reservoirs.setdefault(key, []).append(gap)
            for r, c in slot['cells']:
                weights[r][pair_id] += 1
                weights[n+c][pair_id] += 1
                if r == c:
                    weights[2*n][pair_id] += 1
                if r+c == n-1:
                    weights[2*n+1][pair_id] += 1
    coverage = sum(PARAMETERS['gaps'][:stages])
    for key, gaps in reservoirs.items():
        mask = 1
        for gap in gaps:
            mask |= mask << (gap//2)
        total = sum(gaps)
        require(mask == (1 << (total//2+1))-1, 'complete actual finite subset grid', 'mechanism')
        require(total == (2*degree if key[0] == 'diagonal' else 1)*coverage,
                'ordinary and both amplified diagonal capacities', 'mechanism')
    W = [seq[-1]-seq[0] for seq in lists]
    for line, row in enumerate(weights):
        count = sum(row.values())
        require(count in ((2*degree*stages, 2*degree*stages+2) if line < 2*n
                          else (2*degree*stages,)), 'all-line balanced incidence', 'mechanism')
        variance = sum(w*w*W[slots[pair_id]['stage']]**2 for pair_id, w in row.items())
        require(variance <= 3*degree*sum(x*x for x in W)+4*max(W)**2,
                'all actual stage widths in variance invoice', 'mechanism')
    require(len(entries) == len(occupied) == 2*Q*stages, 'exact fixture entry/position bijection', 'mechanism')
    return {'n': n, 'degree': degree, 'stages': stages, 'pairs_per_stage': Q,
            'distinct_entries_and_cells': len(entries), 'ordinary_reservoirs': degree*n,
            'independent_diagonal_reservoirs': 2, 'ordinary_coverage': coverage,
            'diagonal_coverage': 2*degree*coverage,
            'retained_sha256': digest(b''.join(little_endian(seq) for seq in lists)),
            'complete_square_claim': False}


def reject(action):
    try:
        action()
    except (ValueError, TypeError, KeyError, OSError, UnicodeError, ZeroDivisionError, IndexError):
        return True
    raise ValueError('negative control unexpectedly accepted')


def negative_controls(profiles, bindings):
    count = 0
    for got in profiles:
        for key in ('sum_range_squares', 'max_range', 'variance', 'allocation_upper', 'reserved_entries'):
            altered = copy.deepcopy(got)
            altered[key] += 1
            reject(lambda altered=altered, got=got: verify_profile(got, altered))
            count += 1
        for key in got['stages'][0]:
            altered = copy.deepcopy(got)
            value = altered['stages'][0][key]
            altered['stages'][0][key] = value+1 if type(value) is int else '0'*64
            reject(lambda altered=altered, got=got: verify_profile(got, altered))
            count += 1
        for altered in ({}, [], got['stages'][:-1]):
            reject(lambda altered=altered, got=got: verify_profile(got, altered))
            count += 1
        altered = copy.deepcopy(got)
        altered['stages'][0]['gap'] = True
        reject(lambda altered=altered, got=got: verify_profile(got, altered))
        count += 1
    for gap in (0, 1, 3, 6, 12, -2, True, 2.0):
        reject(lambda gap=gap: gap_check(gap))
        count += 1
    for values, size in (([1, 1, 2], 2), ([3, 2, 1], 2), ([1, 2], 3), ([1, 2], 0), ([1, True], 1)):
        reject(lambda values=values, size=size: choose_window(values, size))
        count += 1
    reject(lambda: complete_grid([2, 8]))
    count += 1
    pairs = [[(59, 61), (71, 73)], [(101, 103), (107, 109)], [(127, 131), (163, 167)]]
    total = pair_control(pairs, [2, 2, 4], 2)
    mutations = []
    for stage, pair, replacement in ((0, 0, (59, 67)), (1, 0, (59, 61)),
                                      (0, 0, (53, 55)), (0, 0, (3, 5))):
        bad = copy.deepcopy(pairs)
        bad[stage][pair] = replacement
        mutations.append(bad)
    mutations.extend((pairs[:-1], [row[:-1] for row in pairs]))
    for bad in mutations:
        reject(lambda bad=bad: pair_control(bad, [2, 2, 4], 2))
        count += 1
    reject(lambda: pair_control(pairs, [2, 2, 4], 2, total+2))
    count += 1
    for left, right in ((0.0, 100), (100, 99), (True, 100)):
        reject(lambda left=left, right=right: protected_interval_count([[59, 71]], [2], 2, left, right))
        count += 1
    for value in ({}, [], None):
        reject(lambda value=value: source_check(value))
        count += 1
    for name in bindings:
        altered = dict(bindings)
        del altered[name]
        reject(lambda altered=altered: source_check(altered))
        count += 1
    for value in ('', 'X'*64, '0'*63, '0'*64, None, True):
        altered = dict(bindings)
        altered[next(iter(SOURCES))] = value
        reject(lambda altered=altered: source_check(altered))
        count += 1
    reject(lambda: source_check(dict(bindings, unexpected='0'*64)))
    count += 1
    for raw in ('', '{', '{"x":1,"x":2}', '{"x":NaN}', '{"x":Infinity}'):
        reject(lambda raw=raw: parse_json(raw))
        count += 1
    return count


def physical_source_attacks(bindings):
    count = 0
    with tempfile.TemporaryDirectory(prefix='sude-finite-prefix-sources-') as tmp:
        root = Path(tmp)
        for name in bindings:
            path = root/name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes((ROOT/name).read_bytes())
        for name in bindings:
            path = root/name
            raw = path.read_bytes()
            for kind in ('missing', 'empty', 'changed', 'directory', 'symlink'):
                path.unlink()
                if kind == 'empty':
                    path.write_bytes(b'')
                elif kind == 'changed':
                    path.write_bytes(raw+b'\nchanged\n')
                elif kind == 'directory':
                    path.mkdir()
                elif kind == 'symlink':
                    path.symlink_to(ROOT/name)
                reject(lambda: source_check(bindings, root))
                count += 1
                if path.is_symlink() or path.is_file():
                    path.unlink()
                elif path.is_dir():
                    path.rmdir()
                path.write_bytes(raw)
        for name in ('code', 'manuscripts'):
            path, backup = root/name, root/(name+'_saved')
            path.rename(backup)
            path.symlink_to(backup, target_is_directory=True)
            reject(lambda: source_check(bindings, root))
            count += 1
            path.unlink()
            backup.rename(path)
        source_check(bindings, root)
    return count


def load_manifest(path):
    raw = regular_bytes(path)
    data = parse_json(raw.decode())
    validate_manifest(data)
    return data, raw


def validate_manifest(data):
    require(type(data) is dict and set(data) == {'schema', 'scope', 'parameters', 'prime_sieve', 'profiles', 'sources'},
            'complete exact manifest fields', 'input')
    require(data['schema'] == SCHEMA and data['scope'] == SCOPE
            and exact_equal(data['parameters'], PARAMETERS), 'canonical finite parameters', 'input')
    source_check(data['sources'])


def manifest_negative_controls(manifest):
    count = 0
    for bad in ({}, [], None):
        reject(lambda bad=bad: validate_manifest(bad))
        count += 1
    for key in manifest:
        bad = copy.deepcopy(manifest)
        del bad[key]
        reject(lambda bad=bad: validate_manifest(bad))
        count += 1
    for key in PARAMETERS:
        bad = copy.deepcopy(manifest)
        value = bad['parameters'][key]
        bad['parameters'][key] = value+1 if type(value) is int else []
        reject(lambda bad=bad: validate_manifest(bad))
        count += 1
    bad = copy.deepcopy(manifest)
    bad['parameters']['degree'] = True
    reject(lambda: validate_manifest(bad))
    count += 1
    for key in ('schema', 'scope'):
        bad = copy.deepcopy(manifest)
        bad[key] += ' changed'
        reject(lambda bad=bad: validate_manifest(bad))
        count += 1
    return count


def run(path):
    require(__debug__, 'run without Python optimization')
    manifest, raw = load_manifest(path)
    B = PARAMETERS['sieve_bound']
    base = odd_sieve(B)
    require(all(prime_at(base, p) == trial_prime(p) for p in range(isqrt(B)+1)),
            'base-prime range independently checked by trial division', 'mechanism')
    primes = array('I', (2*i+1 for i, flag in enumerate(base) if flag and 2*i+1 > 43))
    prime_count = base.count(1)+1
    sieve_result = {'bound': B, 'prime_count': prime_count, 'screened_prime_count': len(primes),
                    'odd_mask_sha256': digest(base), 'screened_prime_sha256': digest(little_endian(primes))}
    require(prime_count == EXPECTED['prime_count'] and exact_equal(sieve_result, manifest['prime_sieve']),
            'complete exact finite prime count and sieve certificate')
    require(prime_count-1 < PARAMETERS['order_min']**2,
            'all selected prime entries in every prescribed input pool')
    require(len(primes) == prime_count-1-PARAMETERS['screened_odd_prime_count'],
            'exact screened-prime subtraction')
    require(complete_grid(PARAMETERS['gaps']) == EXPECTED['coverage']
            and complete_grid(PARAMETERS['gaps'], 2*PARAMETERS['degree']) == 2*PARAMETERS['degree']*EXPECTED['coverage'],
            'ordinary and amplified diagonal complete-grid envelopes')
    bits = 1
    for gap in PARAMETERS['gaps']:
        bits |= bits << (gap//2)
    require(bits == (1 << (EXPECTED['coverage']//2+1))-1,
            'full actual ordinary subset-sum bitset, independent of interval induction', 'mechanism')
    del bits
    require(type(manifest['profiles']) is list and len(manifest['profiles']) == len(PARAMETERS['profiles']),
            'complete fixed alternative profile list')
    profiles, order_results, samples = [], {}, {}
    for profile, expected in zip(PARAMETERS['profiles'], manifest['profiles']):
        got, kept, orders = enumerate_profile(base, primes, profile)
        verify_profile(got, expected)
        profiles.append(got)
        order_results[profile['name']] = orders
        samples[profile['name']] = []
        for n in (2400, 2401, 2417, 2500, 2501, 2750, 2999, 3000):
            row = orders[n-PARAMETERS['order_min']]
            bound = sqrt_upper(F(row['variance'])*log_bounds(8*n+8)[1]/2)
            samples[profile['name']].append(dict(row, allocation_upper=bound))
        del kept
    negatives = negative_controls(profiles, manifest['sources'])+manifest_negative_controls(manifest)
    physical = physical_source_attacks(manifest['sources'])
    mechanisms = {'sieve': sieve_controls(), 'minimum_window': window_controls(),
                  'weighted_permutation': permutation_controls(),
                  'mean_cancellation': cancellation_controls(), 'protected_intervals': interval_controls(),
                  'pair_and_cell_fixture': balanced_fixture()}
    return {'status': 'PASS_EXACT_FINITE_PREFIX_POPULATIONS', 'scope': SCOPE,
            'prime_sieve': sieve_result, 'profiles': profiles, 'all_integer_order_tables': order_results,
            'sample_order_bounds': samples, 'finite_controls': mechanisms,
            'negative_controls': negatives, 'physical_source_attacks': physical,
            'check_counts': dict(COUNTS), 'required_sources': manifest['sources'],
            'input_sha256': digest(raw), 'formal_proof': False,
            'prime_analytic_imports_for_finite_count': [], 'square_cutoff_asserted': False,
            'conditional_interface': 'PB incidence and completion premises as stated in FP5-FP7; no low-order graph, target, or complete-controller claim.'}


if __name__ == '__main__':
    require(len(sys.argv) <= 2, 'at most one manifest path')
    print(json.dumps(run(Path(sys.argv[1]) if len(sys.argv) == 2 else ROOT/INPUT),
                     indent=2, sort_keys=True, allow_nan=False))
