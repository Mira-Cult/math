#!/usr/bin/env python3
"""Exact finite checks for the marked-product approximation barriers."""

from fractions import Fraction


def fwht(values):
    out = list(values)
    step = 1
    while step < len(out):
        for base in range(0, len(out), 2 * step):
            for k in range(base, base + step):
                a, b = out[k], out[k + step]
                out[k], out[k + step] = a + b, a - b
        step *= 2
    return out


def submasks(mask):
    sub = mask
    while True:
        yield sub
        if sub == 0:
            break
        sub = (sub - 1) & mask


def check_case(n, m):
    M, N = 1 << n, n * m
    Q = 1 << N
    F, W = [], []
    for x in range(Q):
        f, w = 1, 1
        for j in range(m):
            block = (x >> (n * j)) & (M - 1)
            f *= -1 if block == 0 else 1
            w *= 2 - M if block == 0 else 2
        F.append(f)
        W.append(w)
    G = F.copy()
    G[0] *= -1
    G[-1] *= -1
    fhat, ghat, what = fwht(F), fwht(G), fwht(W)
    assert all(fhat) and all(ghat)
    assert all(v % (1 << m) == 0 for v in fhat)
    assert all(abs(v) == Q for v in what)
    assert all((w > 0) == (f > 0) for w, f in zip(W, F))
    for s in range(Q):
        assert ghat[s] - fhat[s] == -2 * ((-1) ** m + (-1) ** s.bit_count())
    expected_I = Fraction(2 * n * m, M)
    physical_I = Fraction(sum(G[x] != G[x ^ (1 << i)]
                              for x in range(Q) for i in range(N)), Q)
    fourier_I = Fraction(sum(s.bit_count() * v * v for s, v in enumerate(ghat)), Q * Q)
    assert physical_I == fourier_I == expected_I
    assert sum(G[0] != G[1 << i] for i in range(N)) == 0
    assert sum(G[-1] != G[(Q - 1) ^ (1 << i)] for i in range(N)) == N
    mean = Fraction(sum(G), Q)
    assert mean == Fraction(M - 2, M) ** m - Fraction(2 * ((-1) ** m + 1), Q)
    L = Fraction(3 * M - 4, M) ** m
    assert Fraction(sum(abs(x) for x in fhat), Q) == L
    assert Fraction(sum(abs(w) for w in W), Q) == L
    pairing = Fraction(sum(g * w for g, w in zip(G, W)), Q)
    assert pairing == L - Fraction(2 * ((M - 2) ** m + 2 ** m), Q)
    assert pairing >= L - 4
    gnorm = Fraction(sum(abs(v) for v in ghat), Q)
    assert pairing <= gnorm <= L + 4
    for epsilon in (Fraction(0), Fraction(1, 3), Fraction(1, 2), Fraction(3, 4)):
        # Exact feasible scaling and lower dual certificates; no LP solver.
        assert (1 - epsilon) * L == Fraction(sum(abs((1 - epsilon) * v) for v in fhat), Q)
        assert pairing - epsilon * L >= (1 - epsilon) * L - 4
        assert pairing - epsilon * L <= (1 - epsilon) * gnorm
    core = F.copy()
    core[0] = core[-1] = 0
    core_norm = Fraction(sum(abs(v) for v in fwht(core)), Q)
    assert core_norm >= L - 2
    atoms = [[0] * Q, [0] * Q]
    atoms[0][0] = -2 * F[0]
    atoms[1][-1] = -2 * F[-1]
    pieces = [F] + atoms
    gram = [[Fraction(sum(a * b for a, b in zip(gi, gj)), Q)
             for gj in pieces] for gi in pieces]
    row_sums = [sum(row) for row in gram]
    assert sum(row_sums) == 1
    assert row_sums[1] == row_sums[2] == Fraction(2, Q)
    assert row_sums[1] - gram[1][1] == -Fraction(2, Q)
    cubes, minimum = 0, N
    if N <= 9:
        full = Q - 1
        for fixed in range(Q):
            free = full ^ fixed
            for value in submasks(fixed):
                cubes += 1
                target = G[value]
                if all(G[value | suffix] == target for suffix in submasks(free)):
                    minimum = min(minimum, fixed.bit_count())
                    assert fixed.bit_count() >= m - 1
        assert cubes == 3 ** N
    if m == M:
        assert expected_I == 2 * n
        assert abs(mean) < Fraction(1, 4)
        assert (1 - abs(mean)) / 2 > Fraction(3, 8)
    print(f"PASS n={n} m={m} N={N}: I={expected_I}, dual/norm identities, "
          f"support, Gram; {cubes} subcubes" +
          (f", minimum monochromatic codimension={minimum}" if cubes else ""))
    return cubes


def main():
    total = sum(check_case(n, m) for n, m in ((2, 3), (2, 4), (3, 3), (3, 4)))
    assert total == 26973
    for n in range(2, 11):
        M = 1 << n
        mean = Fraction(M - 2, M) ** M - Fraction(4, M ** M)
        assert abs(mean) < Fraction(1, 4)
        assert Fraction(2 * n * M, M) == 2 * n
        assert Fraction(3 * M - 4, M) >= 2
    print("PASS all exact checks; asymptotic inequalities are proved in the manuscript")


if __name__ == "__main__":
    main()
