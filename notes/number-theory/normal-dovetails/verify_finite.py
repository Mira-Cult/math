#!/usr/bin/env python3
"""Exact finite falsification checks for the generalized-center research paper.

All assertions are ordinary conditionals (also effective under python -O).
No finite check establishes an asymptotic normality theorem.
"""
from fractions import Fraction as F
from math import factorial, comb, isqrt, log2
from hashlib import sha256
import json


def verify(condition, message):
    if not condition:
        raise RuntimeError(message)


def root_floor_of_scaled_rational_power(r, p, q, b, k):
    """Exactly compute floor(b^k * r^(p/q)), r>0, q>0.

    Binary-search comparisons use only integers; no floating point or boundary guess.
    """
    verify(r > 0 and q > 0 and k >= 0 and b >= 2, 'invalid real branch')
    r = F(r)
    if p >= 0:
        num, den = r.numerator**p, r.denominator**p
    else:
        num, den = r.denominator**(-p), r.numerator**(-p)
    a, z = num * pow(b, k * q), den
    lo, hi = 0, 1
    while pow(hi, q) * z <= a:
        lo, hi = hi, hi * 2
    while lo + 1 < hi:
        md = (lo + hi) // 2
        if pow(md, q) * z <= a:
            lo = md
        else:
            hi = md
    verify(pow(lo, q) * z <= a < pow(lo+1, q) * z, 'root floor certificate')
    return lo


def digit_word(floor_scaled, b, K, offset, W):
    verify(0 <= offset and offset + W <= K, 'word out of range')
    return ((floor_scaled % pow(b, K)) // pow(b, K - offset - W)) % pow(b, W)


def binom_real(alpha, n):
    value = F(1)
    for k in range(n):
        value *= (alpha - k) / F(k+1)
    return value


def test_regular_power_recurrences():
    count = 0
    for alpha in (F(0), F(1,2), F(-2), F(3), F(9,7), F(-7,5)):
        seq = [alpha * binom_real(alpha-F(1), n) for n in range(70)]
        for n in range(69):
            verify(F(n+1)*seq[n+1] == (alpha-1-n)*seq[n],
                   f'power recurrence alpha={alpha} n={n}')
            count += 1
        if alpha.denominator == 1 and alpha >= 0:
            verify(all(x == 0 for x in seq[int(alpha):]), 'power polynomial endpoint')
        else:
            verify(all(x != 0 for x in seq), 'power nonexceptional vanishing')
    for theta in (F(0), F(1,2), F(-2), F(3), F(-7,5), F(5,3)):
        seq = [theta]
        for n in range(69):
            seq.append(seq[-1]*F(theta+n+1,n+1))
        for n in range(69):
            verify(F(n+1)*seq[n+1] == (theta+n+1)*seq[n],
                   f'regularized power theta={theta} n={n}')
            count += 1
        if theta.denominator == 1 and theta <= 0:
            verify(all(x == 0 for x in seq[int(-theta):]), 'regularized polynomial endpoint')
        else:
            verify(all(x != 0 for x in seq), 'regularized nonexceptional vanishing')
    return count


def test_window_recurrence():
    # cos x: coefficient vector (c_n,c_(n+1)), with d=2. This test
    # covers long intervening zeros and exact inverse companion matrices.
    cs = [F(0) for _ in range(102)]
    for n in range(102):
        if n % 2 == 0:
            cs[n] = F((-1)**(n//2), factorial(n))
    count = 0
    for n in range(100):
        verify(F((n+2)*(n+1))*cs[n+2]+cs[n] == 0, 'cosine recurrence')
        verify(max(abs(cs[n]), abs(cs[n+1])) != 0, 'coefficient zero window')
        # Backward companion bound ||V_n|| >= 1/[(n+1)!^2] for this example.
        verify(max(abs(cs[n]), abs(cs[n+1])) >= F(1, factorial(n+1)**2),
               'recurrence window quantitative lower bound')
        count += 1
    return count


def test_exact_inverse_identities():
    count = 0
    for a in range(2, 23):
        for n in range(1, a):
            x = F(n, a)
            g = x / (1-x)
            verify(g/(1+g) == x and 1/(1+g) == 1-x, 'inverse cancellation')
            verify((1+x)**3 == F(1)+3*x+3*x*x+x**3, 'integer polynomial')
            count += 1
    return count


def test_algebraic_digits_and_borrows():
    count = 0
    x = F(3,64)
    r = 1+x
    K, W = 20, 3
    # Exception alpha=0 gives integer 1, with all zero fractional digits.
    z0 = root_floor_of_scaled_rational_power(r, 0, 1, 2, K)
    verify(z0 == 2**K, 'exact polynomial constant')
    # epsilon = +/- 1/4096: the first 8 word positions are forced zeros/ones.
    positive = root_floor_of_scaled_rational_power(r, +1, 4096, 2, K)
    negative = root_floor_of_scaled_rational_power(r, -1, 4096, 2, K)
    for t in range(9):
        verify(digit_word(positive,2,K,t,W)==0, f'carry positive t={t}')
        verify(digit_word(negative,2,K,t,W)==7, f'borrow negative t={t}')
        count += 2
    # Family B: (1-x)^(-theta), near theta=0: same two carry directions.
    for theta, target in ((F(1,4096),0),(F(-1,4096),7)):
        val = root_floor_of_scaled_rational_power(F(1)-x,
                                                   -theta.numerator,theta.denominator,2,K)
        for t in range(8):
            verify(digit_word(val,2,K,t,W)==target, f'regularized borrow {theta} {t}')
            count += 1
    # Singular power has exact algebraic digits at theta=+/-1/2.
    y = x/(1-x)
    for p in (+1,-1,+2):
        z = root_floor_of_scaled_rational_power(y,p,2 if p!=2 else 1,2,24)
        verify(z>=0, 'singular algebraic digits')
        if p==2:
            verify(z == (y*y*2**24).__floor__(), 'rational positive-integer power')
        count += 1
    # Terminating boundary: exact rational floor, not a logarithm approximation.
    verify(root_floor_of_scaled_rational_power(F(1,4),1,1,2,10)==256,
           'terminating fractional expansion')
    return count, positive%2**K, negative%2**K


def test_actual_offset_bounds():
    count=0
    n0,d=0,1
    L0=n0+d+10
    L1=L0+d+1
    T=8*(L1+1)
    for r in (10**7, 10**8, 10**10, 10**12):
        B=isqrt(r)
        D=max(1,int(log2(B)//8))
        A=r+B
        K=A*D
        for t in sorted(set([T*B, T*B+1, r//2, r, K-1])):
            if not T*B<=t<=K-1:
                continue
            z=t//(A-1)
            k=z+L0+1  # test dense coefficients; d=1
            verify(3<=k<=D+L1, f'order range r={r} t={t}')
            verify(t-k*(A-1)<=-L0*(A-1), f'upper exponent r={r} t={t}')
            verify(8*(t-k*B)>=5*t, f'lower exponent r={r} t={t}')
            count+=1
    return count


def test_flat_bell_partitions():
    # For q(y)=theta-theta*b^A/(b*y+1) and h=exp(q), the Bell polynomial
    # E_k=h^(k)/h obeys E_k = sum_{ell=1}^k binom(k-1,ell-1)q^(ell)E_(k-ell).
    count=0
    b, A, j = 2,20,3
    z=b*j+1
    for theta in (F(1,3),F(-2,3)):
        qs=[None]
        for ell in range(1,7):
            qs.append(F(((-1)**(ell+1))*theta*factorial(ell)*b**(A+ell), z**(ell+1)))
        E=[F(1)]
        for k in range(1,7):
            E.append(sum((F(comb(k-1,ell-1))*qs[ell]*E[k-ell]
                         for ell in range(1,k+1)),F(0)))
            lead=qs[1]**k
            # For this small x, derivatives of the exponent dominate.
            verify(abs(E[k]-lead)*2 <=abs(lead), f'Bell leading term k={k} theta={theta}')
            count+=1
    return count


def test_repaired_floor_geometry():
    # The offset just before a floor jump falsifies the old -L*r+O(D*B)
    # estimate. Check the corrected exact bound over both sides of each jump.
    count = 0
    for r, B, D in ((10**7, 3000, 2), (10**10, 10**5, 3)):
        A, L = r+B, 13
        K = A*D
        offsets = {104*B, K-1}
        for z in range(D+1):
            offsets.update((z*(A-1)-1, z*(A-1), z*(A-1)+1))
        for t in sorted(offsets):
            if not 104*B <= t <= K-1:
                continue
            k = t//(A-1)+L
            verify(3 <= k <= D+L, 'singular repaired order range')
            verify(t-k*r <= -(L-1)*r+(D+1)*B-2,
                   'singular repaired exact floor upper bound')
            count += 1
        t = A-2
        k = t//(A-1)+L
        verify(t-k*r > -L*r+D*B, 'old stronger floor estimate must fail')
        count += 1
    return count


def test_reciprocal_square_bell():
    # Expand v(y+s)=a/(z+b*s) as a rational formal power series; square
    # it independently of the closed derivative formula in the manuscript.
    count = 0
    for b in (2, 10):
        A, j, order = 16, 3, 8
        a, z = b**A, b*j+1
        v = F(a, z)
        vs = [v * F(-b, z)**ell for ell in range(order+1)]
        vs[0] -= 1  # series for v-1
        for theta in (F(1, 3), F(-2, 3)):
            qs = [None]
            for ell in range(1, order+1):
                coefficient = -theta*sum((vs[i]*vs[ell-i]
                                         for i in range(ell+1)), F(0))
                derivative = factorial(ell)*coefficient
                formula = ((-1)**(ell+1)*theta*factorial(ell)*F(b, z)**ell
                           *((ell+1)*v*v-2*v))
                verify(derivative == formula, 'reciprocal-square derivative formula')
                qs.append(derivative)
                count += 1
            verify(qs[1]*theta > 0, 'reciprocal-square first derivative sign')
            eta = F(4)/(abs(theta)*v*v)
            E = [F(1)]
            for k in range(1, order+1):
                if k >= 2:
                    verify(abs(qs[k]) <= abs(qs[1])**k*factorial(k)*eta**(k-1),
                           'reciprocal-square normalized derivative ratio')
                E.append(sum((F(comb(k-1, ell-1))*qs[ell]*E[k-ell]
                              for ell in range(1, k+1)), F(0)))
                lead = qs[1]**k
                lah = sum((F(factorial(k), factorial(j))*comb(k-1, j-1)*eta**(k-j)
                           for j in range(1, k)), F(0))
                exponential_partial = sum((F(k*k)**s*eta**s/factorial(s)
                                           for s in range(1, k)), F(0))
                verify(abs(E[k]-lead) <= abs(lead)*lah <= abs(lead)*exponential_partial,
                       'reciprocal-square summed Bell/Lah majorant')
                verify(abs(E[k]-lead)*2 <= abs(lead),
                       'reciprocal-square finite leading-term domination')
                count += 1
    return count


def test_nonconstant_exception_borrows():
    # At m=1 both families have nonconstant terminating polynomial endpoints.
    # Family ii uses theta=-m+epsilon, hence exponent m-epsilon.
    count = 0
    b, K, W, m = 2, 14, 2, 1
    x = F(1, 4)
    for sign, target in ((1, 0), (-1, 3)):
        epsilon = F(sign, 256)
        for base, exponent in ((1+x, m+epsilon), (1-x, m-epsilon)):
            z = root_floor_of_scaled_rational_power(base, exponent.numerator,
                                                    exponent.denominator, b, K)
            for t in range(2, 7):
                verify(digit_word(z, b, K, t, W) == target,
                       'nonconstant polynomial endpoint carry convention')
                count += 1
    return count


def main():
    rec=test_regular_power_recurrences()
    wind=test_window_recurrence()
    inv=test_exact_inverse_identities()
    alg,pos,neg=test_algebraic_digits_and_borrows()
    offs=test_actual_offset_bounds()
    bell=test_flat_bell_partitions()
    floor_repairs=test_repaired_floor_geometry()
    square_bell=test_reciprocal_square_bell()
    nonconstant_borrows=test_nonconstant_exception_borrows()
    result={
       'status':'CERTIFIED finite identities ONLY; asymptotic theorem NOT machine-verified',
       'regular_power_recurrences':rec,
       'cosine_window_checks':wind,
       'inverse_polynomial_checks':inv,
       'algebraic_digit_and_borrow_checks':alg,
       'offset_geometry_checks':offs,
       'flat_bell_leading_checks':bell,
       'repaired_singular_floor_checks':floor_repairs,
       'reciprocal_square_bell_checks':square_bell,
       'nonconstant_exception_borrow_checks':nonconstant_borrows,
       'positive_near_exception_20_digits':f'{pos:020b}',
       'negative_near_exception_20_digits':f'{neg:020b}',
       'total_checked':rec+wind+inv+alg+offs+bell+floor_repairs+square_bell+nonconstant_borrows
    }
    print(json.dumps(result,indent=2,sort_keys=True))
    return result


if __name__=='__main__':
    main()
