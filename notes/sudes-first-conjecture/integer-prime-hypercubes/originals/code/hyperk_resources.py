#!/usr/bin/env python3
"""Exact exponent diagnostics for the fixed-k resource lemma; not finite analytics."""
from fractions import Fraction as Q
import argparse
import json


def ledger(k: int, depth: int):
    if isinstance(k, bool) or isinstance(depth, bool) or k < 2 or depth < 0:
        raise ValueError('k >= 2 and finite depth >= 0 required')
    a0, delta = Q(3, 5), Q(1, 5)
    step = Q(3, 20 * (depth + 1))
    last = a0 + depth * step
    margins = {
        'unused_completion': a0-Q(1, 2),
        'occupancy': 1-last,
        'worst_concentrated_deletion': 1-delta-last,
        'midpoint_centering': a0+delta-last,
        'whole_bundle_fluctuation': a0-last/2,
        'rounding': 1+a0,
        'prime_target_vs_X': Q(k)-Q(3, 5)*(k+1),
        'narrow_interval_vs_7_over_12': 1-delta/k-Q(7, 12),
        'macro_matching_divergence': Q(k)-2*delta,
        'seed_supply': Q(1),
    }
    if depth:
        margins['adjacent_capacity'] = step
    if not all(v > 0 for v in margins.values()):
        raise ValueError('nonpositive resource margin')
    assert last == Q(3, 4)-Q(3, 20*(depth+1))
    assert margins['worst_concentrated_deletion'] == Q(1,20)+step
    assert margins['midpoint_centering'] == Q(1,20)+step
    assert margins['whole_bundle_fluctuation'] == Q(9,40)+step/2
    return {'k': k, 'depth': depth, 'first': str(a0), 'last': str(last),
            'step': str(step), 'margins': {a:str(b) for a,b in margins.items()}}


def reject_fixed_endpoint(a):
    # A candidate must have strict power slack to absorb all fixed logs/constants.
    if min(Q(4,5)-a, Q(3,5)-a/2, 1-a) <= 0:
        raise ValueError('endpoint cannot pay all resources')


def self_test():
    count = 0
    for k in range(2,65):
        for depth in (0, 2*k-4, 3*k, 3**k):
            ledger(k, depth)
            count += 1
    rejected = 0
    for a in (Q(4,5),Q(81,100),Q(1),Q(6,5)):
        try:
            reject_fixed_endpoint(a)
        except ValueError:
            rejected += 1
        else:
            raise AssertionError('invalid endpoint accepted')
    for k,d in ((1,1),(0,0),(2,-1),(True,2)):
        try:
            ledger(k,d)
        except ValueError:
            rejected += 1
        else:
            raise AssertionError('bad quantifier domain accepted')
    # A globally sparse set can nevertheless fill an entire line.
    for k in (2,3,5,6):
        n=11
        assert Q(n,n**k) < Q(1,2)
        assert Q(n,n)==1
    return {'exponent_cases':count,'negative_controls':rejected,
            'diagnostics':[ledger(k,2*k-4) for k in (5,6)],
            'scope':'exact exponents only; no finite prime-distribution certification'}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--k',type=int)
    p.add_argument('--depth',type=int)
    a=p.parse_args()
    if a.k is None and a.depth is None:
        result=self_test()
    elif a.k is not None and a.depth is not None:
        result=ledger(a.k,a.depth)
    else:
        p.error('--k and --depth must be supplied together')
    print(json.dumps(result,indent=2))
