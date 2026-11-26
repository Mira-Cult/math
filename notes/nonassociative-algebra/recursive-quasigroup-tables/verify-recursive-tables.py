#!/usr/bin/env python3
"""Exhaustive replay, outputs literal f and D tables."""
import argparse
import itertools

WITNESSES = {
    14: (9, 4, 0, (2, 9, 3, 8, 7, 4, 12, 1, 5, 0, 6, 11, 10)),
    18: (15, 16, 14, (7, 15, 4, 13, 16, 9, 2, 10, 6, 0, 11, 3, 12, 1, 8, 14, 5)),
}

def build_by_columns(n, spec):
    h, a, b, w = spec
    m = n - 1
    columns = [[-1]*n for _ in range(n)]
    # Offsets indexed by d; in column y this fills row x=y-d.
    for y in range(m):
        for d in range(m):
            x = (y-d) % m
            columns[y][x] = m if d == h else (y + w[d] - d) % m
        columns[y][m] = (y+a) % m
    columns[m] = [(x+b) % m for x in range(m)] + [m]
    f = list(zip(*columns))
    # D(x,y) applies column y, then row y.
    dcols = [[f[y][u] for u in columns[y]] for y in range(n)]
    return f, list(zip(*dcols))

def verify(n, f, derivative):
    canonical = list(range(n))
    for a in (f, derivative):
        for L in (*a, *zip(*a)):
            assert sorted(L) == canonical
    codes = [(x, y, f[x][y], derivative[x][y])
             for x,y in itertools.product(canonical, repeat=2)]
    for i,j in itertools.combinations(range(4), 2):
        keys = sorted(n*w[i]+w[j] for w in codes)
        assert keys == list(range(n*n))
    print(f"n={n}: all {4*n} Latin lines and 6 complete pair projections verified")
    return codes

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--tables", action="store_true")
    args = ap.parse_args()
    for n, spec in WITNESSES.items():
        f, d = build_by_columns(n, spec)
        verify(n, f, d)
        if args.tables:
            for name, a in (("f",f),("D",d)):
                print(f"\nn={n}, {name} (alphabet 0..{n-2}; {n-1} denotes infinity)")
                for line in a:
                    print(" ".join(f"{x:2d}" for x in line))
