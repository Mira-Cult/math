# First-band RF/CY stock diagnostic

This is a reproducible comparison of **sufficient envelope inequalities**,
not a claim that actual prime stock is insufficient or that the theorem fails.
It uses the frozen FW checker and input as present at commit
`9924a4a820688071b07f58d8a763db5374602af2`. Their contents last changed
together at `10cb5da79f1296c9d41a580e2d0841bc0102bb23`; SHA-256 values are
`35f703e578115c6c0250f3eca716dfb983a9f173716e1424df3bf0db4ee68184`
for `problems/prime-line-sums/code/cutoff2_controller_far_wide.py` and
`5c24db8b27d325e38a5a060f4b44a1a58455e54f1c0f30c83843126e58c856bb`
for `problems/prime-line-sums/inputs/cutoff2_controller_far_wide_inputs.json`.
The checker validates its pinned helper-source closure on import. The source
and analytic assumptions of that closure are not re-proved by this diagnostic.

For the first FW band and gap two, `n=19483` is the conservative integer
envelope (the first actual odd order is 19485); `V` bounds `log X` above,
`Q` bounds `X/n²` below, and `Xlo` bounds `X` below. The variables `bp` and
`bb` are the frozen normalized prefix and bridge budgets. The code below
compares the frozen central-stock lower envelope with two charges:

- `old`: prefix and bridge plus `2n` preassigned diagonal entries and `3n+1`
  CY exceptional entries, i.e. `5n+1` in total;
- `new`: prefix and bridge plus `2n−1` new diagonal entries and the generic
  Lean RF requirement `6n`, i.e. `8n−1` in total.

The diagonal charge is counted **once**. The frozen budget does not yet
establish coverage of the exact enlarged full reservation, including spare
rectangle cells, for this new route. Its use here is a numerical diagnostic,
not a proof of that physical-value cover. The coarse additional mean shift
`3/(4n)` is added on top of the frozen `sigma` for the three displayed
separation/endpoint margins; this is conservative and is not a new stock
count or a substitution of shifted intervals.

From the repository root, using Python 3.11 or newer:

```sh
python3.11 -B - <<'PY'
import importlib.util, json
from fractions import Fraction as F
from pathlib import Path

s = importlib.util.spec_from_file_location(
    'fw_survey', Path('problems/prime-line-sums/code/cutoff2_controller_far_wide.py'))
m = importlib.util.module_from_spec(s)
s.loader.exec_module(m)
z = json.loads(m.INPUT.read_text())
r = z['bands'][0]['gaps']['2']
p, pp, a, geom, bits, br, bb, bs, bw, _ = m.profile_context(
    0, 2, r['parameters'], r['seed_stages'])
n, V, Q, Xlo = a['n'], a['V'], a['Q'], a['Xlo']
P = r['seed_stages'] + sum(x['count'] for x in r['recipe'])
bp = 2 * p['degree'] * (1 + F(8, n)) * P / n
reserved = br + bb + bp + bw
delta, eps = F(1, pp['delta_denominator']), pp['completion_halfwidth']
beta = max(1 - p['mean_lower'], p['mean_upper'])
beta_b = F(geom['width_factor']) / 4 + max(
    F(1, 2) - p['mean_lower'], p['mean_upper'] - F(1, 2))
sigma = ((beta * bp + beta_b * bb + delta * (bw + br)) / (1 - reserved)
         + F(3, 2) / (n*n*(1 - reserved) - 2*n))
stock = (2*eps - F(1036, 125)*m.H.sqrt_upper(1/Xlo)) / V
old = (bp + bb + F(5*n + 1, n*n)) / Q
new = (bp + bb + F(8*n - 1, n*n)) / Q
for name, value in [
    ('n', n),
    ('separation_margin', min(F(1, 3), F(1, 4) - delta) -
     (sigma + eps + F(3, 4*n))),
    ('left_margin', p['mean_lower'] - (sigma + eps + F(3, 4*n)) - 2/Xlo),
    ('right_margin', 1 - (p['mean_upper'] + sigma + eps + F(3, 4*n))),
    ('old_margin', stock - old), ('new_margin', stock - new),
]:
    print(name, value, 'decimal', float(value))
PY
```

On Python 3.11.14, the old and new margins were respectively approximately
`+7.48748e-7` and `−6.37541e-6`; the latter is exactly
`-4706965182070493700965976248122095020761453424189684622602731/738299499211626879899383361763976008473979431859375000000000000000`.
The separation and endpoint margins were positive, approximately
`0.0541084`, `0.294364`, and `0.316364`. CI's pinned Python 3.12.13 was not
available locally. The output concerns only this frozen profile/envelope.

The distinction comes from CY5–CY6 in
`problems/prime-line-sums/manuscripts/cutoff2_cyclic_residue_centering.md`
versus `Sude.balanced_residual_central_completion` and
`Sude.bmor_balanced_charged_completion`. The latter uses only a generic
degree envelope and charges `6n` when `bits=0`; the former uses special
center-edge trimming and exact rectangle incidence to obtain `3n+1`.
`Sude.central_stock_regular_factor_completion` accepts a supplied factor
and its exact complement count, but, at the frozen diagnostic revision, the
sharper full-keepout factor and its count had not yet been connected in Lean.
In particular, all spare rectangles
must be included in the full geometric count.

**Update, 2026-11-06.** Subsequent Lean checkpoints construct the same-factor
full-keepout count, including spare rectangles, in
[`CYFullKeepoutFactorCount.lean`](../Sude/CYFullKeepoutFactorCount.lean)
(source `724c351def3e17e63aed564bd9d3b991d7e8b8eb`, audit
`2184937cd195a7c1dbc60f887bda65ebf2f3a414`). The
[`CYFullKeepoutSharpCompletion.lean`](../Sude/CYFullKeepoutSharpCompletion.lean)
checkpoint (source `af1d04c403a424821a9b750fead27b5e5a4c789f`, audit
`5fd9968f1d160c64fd871330e00ab9e60114bbe4`) uses this sharp count, and
the conditional diagonal composition appears in
[`CYDiagonalBandCompletion.lean`](../Sude/CYDiagonalBandCompletion.lean)
(source `ebb1a7688bcbdd991ab4c5aaebfde1de4dace198`, audit
`0d43d5a03b5f70a0d0248d85b042ea687fd23df0`). The later
[`FWClassifiedFullCover.lean`](../Sude/FWClassifiedFullCover.lean)
(source `c39f6ee645c5f8f2693f5a366846fa34257c4b31`, audit
`f95f2bfa908f9a84c1441f0937263d82de8d0ad5`) constructs a complete cover
conditional on the same-square role image and spare-cardinality inputs. The
physical same-witness connection, the old-unused-mean and margin bounds, and
the numerical stock gate remain unresolved; the diagnostic above retains its
original sufficient-envelope scope and does not establish them.

**Coarse mean-certificate diagnostic, 2026-11-06.** At source revision
`cf92ecb00cc2254b2773d571aa67b78f7b6f8b32`, the normalized
[quarter-reservation bound](../Sude/FWFullReservationQuarterCapacity.lean)
and the global-mean and entry-range estimates used in the
[spare-value bound](../Sude/FWSpareGlobalDeviationOfTheta.lean) give the
following candidate sufficient enclosure on one supplied square, under their
stated theta, index and packing hypotheses. Let `N=n²`, let `B` be the
cardinality of the **entire** full reservation, including every spare corner,
and let `X=poolMaximum n`. If `B≤N/4` and each reserved value differs from
the global mean by at most `257X/500`, the complement-mean identity gives
`|μunused−m|≤(257/500)X·B/(N−B)≤(257/1500)X`. This is a mathematical
sufficient estimate; its combination has not been formalized as a Lean theorem
or proved sharp.

For the frozen first-band `ε=4262317/50000000`, its proposed `σ=257/1500`
already exceeds the strict quarter-separation allowance even at `w=0`, before
adding the positive `3/(4n)` term. The rational arithmetic is reproducible:

```sh
python3.11 - <<'PYMEAN'
from fractions import Fraction as F
sigma, eps = F(257, 1500), F(4262317, 50000000)
print(sigma + eps - F(1, 4), float(sigma + eps - F(1, 4)))
PYMEAN
```

The result is `986951/150000000` (approximately `0.00657967`). This only
shows that this **coarse sufficient certificate** cannot verify that
separation inequality with the frozen ε. It says nothing about the actual
unused mean, the existence of a sharper bound, or the theorem's truth.

A separate finite counterexample shows that the CY bound cannot be inferred
from the generic degree interface alone. For `n=71`, `r₀=1`, `bits=2`, let
the reservation be both diagonals plus the cells `(r,(2r+t) mod 71)` for
`0≤r<35`, `0≤t<10`. The command below returns `487 1 12 6 7 365`: the
reservation size, row-degree minimum/maximum, column-degree minimum/maximum,
and a lower bound for the complement of any regular factor. The generic load
condition is `4*(1+6*2+4)=68≤71`; any factor has degree at most `71−12=59`,
so its complement has at least 365 cells, exceeding `3*71+1=214`. This is
not a counterexample to CY's stronger rectangle-incidence hypotheses.

```sh
python3.11 -c 'n=71;R={(r,r) for r in range(n)}|{(r,n-1-r) for r in range(n)}|{(r,(2*r+t)%n) for r in range(n//2) for t in range(10)};rows=[sum((r,c) in R for c in range(n)) for r in range(n)];cols=[sum((r,c) in R for r in range(n)) for c in range(n)];print(len(R),min(rows),max(rows),min(cols),max(cols),n*n-len(R)-n*(n-max(rows)))'
```
