"""Exact evaluation of the seven local hole cells; no solver dependencies."""
from itertools import permutations, product

centres = sorted({
    xyz
    for seed in [(1, 1, 1), (1, 1, 5), (2, 2, 5)]
    for phase in [seed, tuple((x+3) % 6 for x in seed)]
    for xyz in permutations(phase)
    if xyz[2] <= 3
})
assert centres == [(1,1,1), (1,5,1), (2,5,2), (4,4,2),
                   (5,1,1), (5,2,2), (5,5,2)]
def constraints(center, r):
    """Tuple keys give coefficients of offsets (A,B,C,D), right side inclusive."""
    a,b,c = center
    result = {}
    for j,k,l in product(range(-1,2), range(3), range(3)):
        leading = (a-6*j-3*l,b-6*k+3*l,c-3*l)
        p = sum(max(0,x) for x in leading)
        n = sum(max(0,-x) for x in leading)
        if p > 2 or n > 6:
            continue
        assert all(leading)
        c0 = (-(r+1)*j-k-(r//2)*l, j-r*k+((r+1)//2)*l,
              k-((r+3)//2)*l)
        if p == 2:
            assert n < 6
            positive = tuple(int(x>0) for x in leading)
            key = positive+(1,)
            value = r+1-l-sum(u*v for u,v in zip(positive,c0))
        else:
            assert n == 6
            negative = tuple(int(x<0) for x in leading)
            key = tuple(-x for x in negative)+(0,)
            value = r+sum(u*v for u,v in zip(negative,c0))
        assert key not in result
        result[key] = value
    assert len(result) == 4
    return result

def ceil3(x): return -((-x)//3)

def optimize(center,S):
    # Read D + sum of positive subset >= bound, or sum subset <= bound.
    def lower(a,b,c): return S[(a,b,c,1)]
    def upper(a,b,c): return -S[(-a,-b,-c,0)]
    if center == (1,1,1):
        ab,ac,bc,s = lower(1,1,0),lower(1,0,1),lower(0,1,1),upper(1,1,1)
        d = ceil3(ab+ac+bc-2*s)
        c = ac+bc-2*d-s
        a,b = ac-d-c,bc-d-c
    elif center == (1,5,1):
        ac,bb,s,t = lower(1,0,1),lower(0,1,0),upper(0,1,1),upper(1,1,0)
        d = ceil3(ac+2*bb-s-t)
        b = bb-d
        c = ac-d-t+b
        a = ac-d-c
    elif center == (4,4,2):
        ab,cc,s,t = lower(1,1,0),lower(0,0,1),upper(0,1,1),upper(1,0,1)
        d = ceil3(ab+2*cc-s-t)
        c = cc-d
        b = ab-d-t+c
        a = ab-d-b
    elif center == (5,1,1):
        aa,bc,s,t = lower(1,0,0),lower(0,1,1),upper(1,0,1),upper(1,1,0)
        d = ceil3(bc+2*aa-s-t)
        a = aa-d
        c = bc-d-t+a
        b = bc-d-c
    else:
        aa,bb,cc,s = lower(1,0,0),lower(0,1,0),lower(0,0,1),upper(1,1,1)
        d = ceil3(aa+bb+cc-s)
        a,b,c = aa-d,bb-d,cc-d
    v = (a,b,c,d)
    assert all(sum(i*j for i,j in zip(k,v))>=rhs for k,rhs in S.items())
    return v

if __name__ == "__main__":
    for r in range(6):
        candidates = []
        for center in centres:
            a,b,c = center
            A,B,C,D = optimize(center,constraints(center,r))
            candidates.append((D,c,C,b,B,a,A))
        D,c,C,b,B,a,A = min(candidates)
        print(f"r={r}: (units,H,B,C) = ({a}t+{A}, {b}t+{B}, {c}t+{C}, 4t+{D})")
