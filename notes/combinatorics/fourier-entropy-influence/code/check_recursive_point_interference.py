#!/usr/bin/env python3
"""Certified finite checks for the recursive uniform-9/2 FEI theorem.

Integer Walsh transforms and physical edge counts are independent of the
proof recurrence. Entropy and pointed-invariant comparisons use exact rational
intervals for logarithms, obtained from the atanh series with a proved tail
bound. No floating-point comparison is used for a PASS assertion.
"""

from fractions import Fraction as Q
from functools import lru_cache


def walsh(values):
    out = list(values)
    step = 1
    while step < len(out):
        for base in range(0, len(out), 2*step):
            for j in range(step):
                x, y = out[base+j], out[base+j+step]
                out[base+j], out[base+j+step] = x+y, x-y
        step *= 2
    return out


def edge_count(values, n):
    return sum(values[x] != values[x ^ (1 << i)]
               for x in range(1 << n) for i in range(n))


def ln_interval_unit(u, terms=24):
    assert Q(1) <= u <= Q(2)
    t = (u-1)/(u+1)
    lo = 2*sum((t**(2*j+1))/Q(2*j+1) for j in range(terms))
    tail = 2*t**(2*terms+1)/(Q(2*terms+1)*(1-t*t))
    return lo, lo+tail


LN2 = ln_interval_unit(Q(2))


@lru_cache(None)
def log2_interval(value):
    assert isinstance(value, int) and value > 0
    power = value.bit_length()-1
    u = Q(value, 1 << power)
    low, high = ln_interval_unit(u)
    return Q(power)+low/LN2[1], Q(power)+high/LN2[0]


def linear_log_interval(terms):
    low = high = Q(0)
    for value, coefficient in terms:
        a, b = log2_interval(value)
        if coefficient >= 0:
            low += coefficient*a
            high += coefficient*b
        else:
            low += coefficient*b
            high += coefficient*a
    return low, high


def certify(values, n):
    size = 1 << n
    w = walsh(values)
    assert all(v != 0 for v in w)
    assert all(v % 4 == 2 for v in w)
    edges = edge_count(values, n)
    influence = Q(edges, size)
    assert sum(mask.bit_count()*v*v for mask, v in enumerate(w)) == size*edges
    llo, lhi = linear_log_interval([(abs(v), Q(2*v*v, size*size)) for v in w])
    entropy = Q(2*n)-lhi, Q(2*n)-llo
    c = values[0]
    a = [c*v for v in w]
    assert sum(a) == size
    blo, bhi = linear_log_interval([(abs(v), Q(2*(v-1), size)) for v in a])
    sensitivity = sum(values[0] != values[1 << i] for i in range(n))
    t = n-2*sensitivity
    cfei, alpha, delta = Q(9, 2), Q(4, 7), Q(2, size)
    ulo, uhi = 2*blo-cfei*t, 2*bhi-cfei*t
    margin_lo = cfei*influence-entropy[1]
    target_hi = delta*(alpha+max(abs(ulo), abs(uhi))/3)
    assert margin_lo >= target_hi
    return w, influence


def build(tree, counts):
    if isinstance(tree, int):
        assert tree >= 2
        values = [1]*(1 << tree)
        values[0] = -1
        certify(values, tree)
        counts[0] += 1
        return tree, values
    assert len(tree) >= 2
    children = [build(child, counts) for child in tree]
    n = sum(bits for bits, _ in children)
    product = []
    for x in range(1 << n):
        pos, value = 0, 1
        for bits, vals in children:
            value *= vals[(x >> pos) & ((1 << bits)-1)]
            pos += bits
        product.append(value)
    values = list(product)
    values[0] *= -1
    wf = walsh(product)
    wg, ig = certify(values, n)
    c = product[0]
    assert all(v and v % 4 == 0 for v in wf)
    assert all(wg[i] == wf[i]-2*c for i in range(1 << n))
    for old, new in zip(wf, wg):
        a = c*old
        assert -c*new == 2-a
    # Integer certification of the scalar score correction <=3.
    for a in set(c*v for v in wf):
        if a > 0:
            assert pow(a, a-1) <= 8*pow(a-2, a-1)
        else:
            assert pow(abs(a-2), 1-a) <= 8*pow(abs(a), 1-a)
    sf = sum(product[0] != product[1 << i] for i in range(n))
    assert edge_count(values, n)-edge_count(product, n) == 2*(n-2*sf)
    for bits, _ in children:
        assert Q(2, 1 << bits) >= 4*Q(2, 1 << n)
    counts[1] += 1
    return n, values


def main():
    assert LN2[0] > Q(2, 3)
    cases = [2, 3, [2, 2], [2, 3, 4], [[2, 2], [2, 2]],
             [[2, 2], 2, 3], [[[2, 2], 2], [2, 2]],
             [[3, 3], [2, 2]], [[2, 2, 2], [2, 2, 2]]]
    counts = [0, 0]
    max_n = 0
    for tree in cases:
        n, _ = build(tree, counts)
        max_n = max(max_n, n)
        print(f"PASS certified invariant: {tree}; N={n}")
    print(f"PASS: {len(cases)} trees; {counts[0]} leaf and {counts[1]} internal node checks; max N={max_n}")
    print("Logarithm intervals: 24 atanh terms, exact rational tail bounds.")


if __name__ == '__main__':
    main()
