#!/usr/bin/env python3
"""Exact/certified checks for uniform marked-set FEI closure.

Self-contained Python 3 standard library. Truth tables, Walsh transforms,
edge counts, and linear identities among logarithms are exact. Logarithms
are factored into primes, then enclosed by rational atanh-series bounds.
There are no floating-point PASS decisions.

The general theorem is proved in marked_set_closure.md; these finite checks
test its identities and constants, not the universal quantifiers.
"""

from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations


def walsh(values):
    out = list(values)
    step = 1
    while step < len(out):
        for base in range(0, len(out), 2 * step):
            for j in range(step):
                a, b = out[base + j], out[base + j + step]
                out[base + j], out[base + j + step] = a + b, a - b
        step *= 2
    return out


def chi(mask, point):
    return 1 if (mask & point).bit_count() % 2 == 0 else -1


def edge_count(values, n):
    return sum(values[x] != values[x ^ (1 << i)]
               for x in range(1 << n) for i in range(n))


def ln_unit_interval(u, terms=24):
    assert Q(1) <= u <= Q(2)
    t = (u - 1) / (u + 1)
    lower = 2 * sum(t ** (2 * j + 1) / Q(2 * j + 1)
                    for j in range(terms))
    tail = 2 * t ** (2 * terms + 1) / (Q(2 * terms + 1) * (1 - t * t))
    return lower, lower + tail


LN2 = ln_unit_interval(Q(2))


@lru_cache(None)
def log2_interval(value):
    assert isinstance(value, int) and value > 0
    if value == 2:
        return Q(1), Q(1)
    exponent = value.bit_length() - 1
    low, high = ln_unit_interval(Q(value, 1 << exponent))
    return Q(exponent) + low / LN2[1], Q(exponent) + high / LN2[0]


@lru_cache(None)
def prime_factors(value):
    assert value > 0
    factors = []
    p = 2
    while p * p <= value:
        exponent = 0
        while value % p == 0:
            value //= p
            exponent += 1
        if exponent:
            factors.append((p, exponent))
        p = 3 if p == 2 else p + 2
    if value > 1:
        factors.append((value, 1))
    return tuple(factors)


class LogForm:
    """Exact rational linear combination of log_2(prime), including log_2(2)."""

    def __init__(self, terms=None):
        self.terms = {p: Q(c) for p, c in (terms or {}).items() if c}

    @classmethod
    def constant(cls, value):
        return cls({2: Q(value)})

    @classmethod
    def log(cls, value):
        return cls(dict(prime_factors(value)))

    @classmethod
    def weighted_logs(cls, pairs):
        combined = Counter()
        for value, coefficient in pairs:
            combined[value] += coefficient
        terms = Counter()
        for value, coefficient in combined.items():
            if coefficient:
                for p, exponent in prime_factors(value):
                    terms[p] += coefficient * exponent
        return cls(terms)

    def __add__(self, other):
        if not isinstance(other, LogForm):
            other = LogForm.constant(other)
        out = self.terms.copy()
        for p, coefficient in other.terms.items():
            out[p] = out.get(p, Q(0)) + coefficient
        return LogForm(out)

    __radd__ = __add__

    def __neg__(self):
        return self * -1

    def __sub__(self, other):
        return self + (-other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, scalar):
        return LogForm({p: coefficient * scalar
                        for p, coefficient in self.terms.items()})

    __rmul__ = __mul__

    def __eq__(self, other):
        if not isinstance(other, LogForm):
            other = LogForm.constant(other)
        return self.terms == other.terms

    def interval(self):
        low = high = Q(0)
        for p, coefficient in self.terms.items():
            a, b = log2_interval(p)
            if coefficient >= 0:
                low += coefficient * a
                high += coefficient * b
            else:
                low += coefficient * b
                high += coefficient * a
        return low, high

    def max_abs(self):
        a, b = self.interval()
        return max(abs(a), abs(b))


def base_statistics(values):
    size = len(values)
    n = size.bit_length() - 1
    assert size == 1 << n and n >= 2
    assert all(v in (-1, 1) for v in values)
    w = walsh(values)
    assert all(w) and all(v % 2 == 0 for v in w)
    assert sum(v * v for v in w) == size * size
    edges = edge_count(values, n)
    influence = Q(edges, size)
    assert sum(s.bit_count() * v * v for s, v in enumerate(w)) == size * edges
    entropy = 2 * n - LogForm.weighted_logs(
        (abs(v), Q(2 * v * v, size * size)) for v in w)
    return dict(values=values, w=w, n=n, size=size, I=influence, H=entropy)


def mark_statistics(base, marks, cfei):
    values, w, n, size = (base[k] for k in ('values', 'w', 'n', 'size'))
    q = len(marks)
    assert q >= 2 and len(set(marks)) == q
    assert all(0 <= x < size for x in marks)
    delta = Q(2, size)
    d = [sum(values[x] * chi(s, x) for x in marks) for s in range(size)]
    assert sum(v * v for v in d) == size * q
    assert sum(a * b for a, b in zip(d, w)) == size * q
    score = LogForm.weighted_logs(
        (abs(a), delta * b * (a - b)) for a, b in zip(w, d))
    cross = LogForm.weighted_logs(
        (abs(a), delta * (b * b - q)) for a, b in zip(w, d))
    point_scores = []
    point_t = []
    for x in marks:
        c = values[x]
        aligned = [c * chi(s, x) * a for s, a in enumerate(w)]
        assert sum(aligned) == size
        point_scores.append(LogForm.weighted_logs(
            (abs(a), delta * (a - 1)) for a in aligned))
        sensitivity = sum(values[x] != values[x ^ (1 << i)] for i in range(n))
        point_t.append(n - 2 * sensitivity)
    assert score == sum(point_scores, LogForm()) - cross
    internal = sum(values[x] * values[y] for x, y in combinations(marks, 2)
                   if (x ^ y).bit_count() == 1)
    boundary = sum(point_t) - 2 * internal
    markset = set(marks)
    actual_boundary = sum(values[x] * values[x ^ (1 << i)]
                          for x in marks for i in range(n)
                          if x ^ (1 << i) not in markset)
    assert boundary == actual_boundary and abs(boundary) <= q * n
    out = dict(base)
    out.update(marks=tuple(marks), q=q, delta=delta, d=d, P=score, K=cross,
               E=internal, T=boundary, B=point_scores, t=point_t,
               U=2 * score - cfei * boundary, V=cross - cfei * internal,
               margin=cfei * base['I'] - base['H'], C=cfei)
    return out


def invariant(stats):
    q, delta = stats['q'], stats['delta']
    beta = Q(1, 4 * q * q - 1)
    target = delta * (Q(1, 20) + beta * stats['U'].max_abs()
                      + 2 * beta * stats['V'].max_abs())
    lower, _ = stats['margin'].interval()
    assert lower >= target, (stats['n'], q, stats['marks'], lower, target)


def certify_modification(old, new, separated):
    size, delta, q = old['size'], old['delta'], old['q']
    assert old['marks'] == new['marks']
    assert all(b == a - 2 * d for a, b, d in zip(old['w'], new['w'], old['d']))
    assert new['d'] == [-d for d in old['d']]
    assert new['I'] - old['I'] == delta * old['T']
    assert new['T'] == -old['T'] and new['E'] == old['E']
    divergence = LogForm()
    remainder = LogForm()
    change_cross = LogForm()
    for a, b, d in zip(old['w'], new['w'], old['d']):
        logratio = LogForm.log(abs(b)) - LogForm.log(abs(a))
        divergence += Q(2 * b * b, size * size) * logratio
        remainder += -delta * d * (a - d) * logratio
        change_cross += delta * (d * d - q) * logratio
    assert new['H'] == old['H'] + 2 * delta * old['P'] - divergence
    assert new['P'] == -old['P'] + remainder
    assert new['K'] - old['K'] == change_cross
    assert divergence.interval()[0] >= 0
    if separated:
        assert min(abs(a) for a in old['w']) >= 4 * q
        assert remainder.interval()[0] > 0
        assert remainder.interval()[1] <= 6 * q
        for a, b in zip(old['w'], new['w']):
            assert 4 * b * b >= a * a and 4 * b * b <= 9 * a * a
        assert old['K'] == 0 and old['E'] == 0 and new['E'] == 0
        assert new['V'].max_abs() <= 2 * q * (q - 1)
        if q == 2:
            assert new['V'].max_abs() <= 2
            active = [s for s, d in enumerate(old['d']) if d]
            assert len(active) * 2 == size
            assert all(old['w'][s] % 8 == 0 for s in range(size))
            assert all(new['w'][s] % 8 == 4 for s in active)
            assert all(new['w'][s] % 8 == 0 for s in range(size) if s not in set(active))


def modified(stats):
    values = list(stats['values'])
    for x in stats['marks']:
        values[x] *= -1
    return mark_statistics(base_statistics(values), stats['marks'], stats['C'])


COUNTS = Counter()


def product_node(children, cfei):
    q = children[0]['q']
    m = len(children)
    assert all(child['q'] == q for child in children)
    assert m >= 2 + (q - 1).bit_length()
    n = sum(child['n'] for child in children)
    marks = [0] * q
    pos = 0
    for child in children:
        for a, x in enumerate(child['marks']):
            marks[a] |= x << pos
        pos += child['n']
    for x, y in combinations(marks, 2):
        assert (x ^ y).bit_count() >= m
    values = []
    for x in range(1 << n):
        pos, value = 0, 1
        for child in children:
            value *= child['values'][(x >> pos) & (child['size'] - 1)]
            pos += child['n']
        values.append(value)
    old = mark_statistics(base_statistics(values), marks, cfei)
    assert old['H'] == sum((child['H'] for child in children), LogForm())
    assert old['I'] == sum(child['I'] for child in children)
    assert old['K'] == 0 and old['E'] == 0
    assert old['P'] == sum((child['P'] + child['K'] for child in children), LogForm())
    assert old['T'] == sum(child['T'] + 2 * child['E'] for child in children)
    assert old['U'] == sum((child['U'] + 2 * child['V'] for child in children), LogForm())
    for child in children:
        assert child['delta'] >= 4 * q * q * old['delta']
    new = modified(old)
    certify_modification(old, new, separated=True)
    invariant(new)
    COUNTS['internal_nodes'] += 1
    COUNTS['maximum_n'] = max(COUNTS['maximum_n'], n)
    return new


def rare_leaf(n, second=None, q=2, cfei=Q(4)):
    values = [1] * (1 << n)
    values[0] = -1
    marks = (0, second if second is not None else (1 << n) - 1) if q == 2 else tuple(range(q))
    stats = mark_statistics(base_statistics(values), marks, cfei)
    invariant(stats)
    if q == 2:
        assert stats['P'] == 0 and stats['T'] == 0
        expected_k = -2 * stats['delta'] * LogForm.log((1 << (n - 1)) - 1)
        assert stats['K'] == expected_k
        assert stats['I'] == n * stats['delta']
        if cfei == 4:
            assert stats['V'].max_abs() <= 5
            assert stats['margin'].interval()[0] > stats['delta']
        moved = modified(stats)
        certify_modification(stats, moved, separated=False)
        assert moved['H'] == stats['H'] and moved['I'] == stats['I']
    COUNTS['rare_leaves'] += 1
    return stats


def check_finite_leaf_envelopes():
    # All positive Boolean functions on 2 or 3 bits, and all unordered
    # marked sets of every cardinality q>=2. Scores are symmetric in marks.
    functions = marked_cases = 0
    for n in (2, 3):
        size = 1 << n
        for truth_mask in range(1 << size):
            values = [-1 if truth_mask & (1 << x) else 1 for x in range(size)]
            if not all(walsh(values)):
                continue
            base = base_statistics(values)
            assert (4 * base['I'] - base['H']).interval()[0] >= 0
            functions += 1
            for q in range(2, size + 1):
                for marks in combinations(range(size), q):
                    stats = mark_statistics(base, marks, Q(12))
                    invariant(stats)
                    marked_cases += 1
    print(f"PASS exhaustive leaf preparation: {functions} positive Boolean functions; "
          f"{marked_cases} marked sets; n=2,3; all q>=2; C0=4,C=12")


def check_rare_trees():
    # All locations of the second mark, including adjacency, through n=7.
    for n in range(2, 8):
        for second in range(1, 1 << n):
            rare_leaf(n, second)
    # Nontrivial recursion, different child dimensions, mixed adjacency.
    a = product_node([rare_leaf(2, 1), rare_leaf(2, 2), rare_leaf(2, 3)], Q(4))
    product_node([a, rare_leaf(2, 1), rare_leaf(2, 3)], Q(4))
    product_node([rare_leaf(3, 1), rare_leaf(3, 3), rare_leaf(3, 7)], Q(4))
    product_node([rare_leaf(2, 1), rare_leaf(3, 1), rare_leaf(4, 15)], Q(4))
    product_node([a, rare_leaf(3, 1), rare_leaf(3, 7)], Q(4))
    print("PASS rare-point C=4: all distinct second marks through n=7; "
          "five internal-node cases, including depth two and adjacent leaf marks")


def check_generic_q_nodes():
    for q in (2, 3, 4, 5, 8):
        n = max(2, (q - 1).bit_length())
        m = 2 + (q - 1).bit_length()
        children = [rare_leaf(n, q=q, cfei=Q(12)) for _ in range(m)]
        parent = product_node(children, Q(12))
        assert parent['n'] == n * m
        print(f"PASS generic marked-set node: q={q}, m={m}, N={n*m}, C=12")
    # All q leaves are already prepared by the exhaustive test; alter
    # marks and signs to test that no rare-point sign cancellation is used.
    children = []
    for truth_mask, marks in ((1, (0, 1, 2)), (7, (3, 2, 1)),
                              (11, (1, 0, 3)), (13, (2, 3, 0))):
        values = [-1 if truth_mask & (1 << x) else 1 for x in range(4)]
        stats = mark_statistics(base_statistics(values), marks, Q(12))
        invariant(stats)
        children.append(stats)
    product_node(children, Q(12))
    print("PASS generic nonidentical signed leaves with q=3")


def check_full_interaction():
    for m in range(3, 7):
        parent = product_node([rare_leaf(2, 3) for _ in range(m)], Q(4))
        size, n = parent['size'], parent['n']
        top = LogForm.weighted_logs(
            (abs(a), Q(2 * chi(size - 1, s), size))
            for s, a in enumerate(parent['w']))
        # lambda=4/2^m. Write the predicted expression using integer logs
        # so that equality is exact after prime factorization.
        z = 1 << m
        aform = Q(1, 2) * (LogForm.log(z - 4) + LogForm.log(z + 4)
                           - 2 * LogForm.log(z))
        bform = Q(1, 2) * (LogForm.log(z - 4) - LogForm.log(z + 4))
        epsilon = -1 if m % 2 else 1
        expected = epsilon * (aform + Q(2, z) * bform)
        assert top == expected
        assert aform.interval()[1] < 0 and bform.interval()[1] < 0
        assert (epsilon * top).interval()[1] < 0
        assert parent['I'] == m
        assert n == 2 * m
    print("PASS exact full logarithmic interaction: m=3,4,5,6; N=2m")


def check_uniform_scalar_algebra():
    assert LN2[0] > Q(2, 3)
    # Polynomial identities prove the inequalities for all q; this finite
    # loop additionally guards the displayed substitutions and constants.
    for q in range(2, 1001):
        m = 2 + (q - 1).bit_length()
        r, beta = 4 * q * q, Q(1, 4 * q * q - 1)
        assert 4 ** (m - 1) >= r
        assert Q(r * m - 1, 20) - beta * (4 * q * q + 8 * q) >= Q(13, 60)
        e = min(Q(q, 2), Q(q * (q - 1), 4))
        assert beta * (8 * q * q + 24 * q) <= Q(16, 3)
        assert beta * (q + 2 * e) <= Q(1, 5)
    for c0 in (Q(0), Q(4), Q(14), Q(1, 3), Q(17)):
        c = Q(5, 4) * c0 + 7
        assert c - c0 - (Q(1, 40) + Q(16, 3) + c / 5) == Q(29, 120)
    print("PASS scalar constant identities; q=2..1000; exact rational arithmetic")


def main():
    check_uniform_scalar_algebra()
    check_finite_leaf_envelopes()
    check_rare_trees()
    check_generic_q_nodes()
    check_full_interaction()
    print(f"PASS totals: {COUNTS['rare_leaves']} rare-leaf instances; "
          f"{COUNTS['internal_nodes']} internal nodes; maximum N={COUNTS['maximum_n']}")
    print("Logarithm bounds: 24 atanh terms with rational tail intervals; "
          "all identity comparisons exact after prime factorization.")


if __name__ == '__main__':
    main()
