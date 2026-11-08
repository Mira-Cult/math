"""Specialize the bounded-width unmatched-label matching DP to the P5 gadgets.

This is derived from the graph construction, not the recovered endpoint-color DP.
"""
from collections import defaultdict
from random import Random
from check_gadget import permanent, matching_sum, gadget


def profile_permanent(u, v, t):
    n = len(u)
    assert len(v) == n
    # Counters are unmatched RU,RV,CU,CV,CT endpoints. A dense implementation
    # stores only four, recovering CT from the left/right balance equation.
    states = {(0,0,0,0,0): 1}
    for i in range(n):
        row = defaultdict(int)
        for (ru,rv,cu,cv,ct), w in states.items():
            assert ru + rv == cu + cv + ct
            row[(ru+1,rv,cu,cv,ct)] += w*u[i]
            if cu:
                row[(ru,rv,cu-1,cv,ct)] += w*u[i]*cu
            row[(ru,rv+1,cu,cv,ct)] += w
            if cv:
                row[(ru,rv,cu,cv-1,ct)] += w*cv
            if ct:
                row[(ru,rv,cu,cv,ct-1)] += w*t*ct
        col = defaultdict(int)
        for (ru,rv,cu,cv,ct), w in row.items():
            assert ru + rv == cu + cv + ct + 1
            col[(ru,rv,cu+1,cv,ct)] += w
            if ru:
                col[(ru-1,rv,cu,cv,ct)] += w*ru
            col[(ru,rv,cu,cv+1,ct)] += w*v[i]
            if rv:
                col[(ru,rv-1,cu,cv,ct)] += w*v[i]*rv
            col[(ru,rv,cu,cv,ct+1)] += w
        states = {s:w for s,w in col.items() if w}
    return states.get((0,0,0,0,0), 0)


def main():
    r = Random(20261108)
    cases = 0
    for n in range(9):
        for _ in range(20):
            u = [r.randrange(-4,5) for _ in range(n)]
            v = [r.randrange(-4,5) for _ in range(n)]
            t = r.randrange(-4,5)
            actual = profile_permanent(u,v,t)
            expected = permanent(u,v,t)
            assert actual == expected, (u,v,t,actual,expected)
            if n <= 4:
                assert actual == matching_sum(gadget(u,v,t))
            cases += 1
    print(f'{cases} profile/permutation checks passed; 100 also checked against exhaustive gadget matchings.')


if __name__ == '__main__':
    main()
