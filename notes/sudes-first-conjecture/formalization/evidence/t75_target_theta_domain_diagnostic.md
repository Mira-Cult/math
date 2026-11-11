# T75 nominal target window and finite BMOR theta domain

This diagnostic compares the first-band nominal **target-line** window with
the explicit domain of the `BMORFiniteTheta` input used by the Lean entry-pool
arguments. It is a domain comparison; it does not assert that the target prime
supply is impossible or that other analytic results cannot establish it.
The source revision examined is `a9a4ef0b5a6ed6bd6c9333ed08e45ba9ce6daa12`.

Set `X = poolMaximum n`, `μ = centralEntriesMean (prescribedPoolValues n)
centralPoolValue`, `y = n μ`, and `D = y/1240`, as in
[`FWSelectedEnrichedT75NominalRepair.lean`](../Sude/FWSelectedEnrichedT75NominalRepair.lean).
The conversion from this μ to the Lucas total uses
[`prescribedPoolValues_mean`](../Sude/ReservedPoolMean.lean). For
`19485 ≤ n ≤ 21248`, assuming the explicit `BMORFiniteTheta`,
`RSIndexLower` and `RSIndexUpper` inputs,
[`fw_actual_pool_mean_bounds_of_theta`](../Sude/FWThetaInputs.lean) gives
`μ ≥ (243/500) X`, and the lower-index estimate
[`fw_poolMaximum_gt_four_seed`](../Sude/FWPoolBound.lean) gives
`X > 4·2³⁰`. Hence

```
y − D > 19485 · (243/500) · (4·2³⁰) · (1239/1240)
      = 157477266870239232/3875 > 4·10¹³.
```

[`BMORFiniteTheta`](../Sude/BMORFinite.lean) requires its endpoint to be no
greater than the modulus-dependent `bmorLimit q`; the encoded base and
one-step limits are all at most `4·10¹³`. The direct modulus-two cutoff is
`10¹²`; the separate modulus-two reduction uses modulus-four classes through
`4·10¹³`. Therefore neither a
pointwise use of that finite input at a nominal target-window point nor its
modulus-two reduction applies directly there. It may still be used at smaller
scales, as it is for the mean estimate; this comparison does not rule out a
different use of those bounds or any other applicable theorem.

The corrected
[T75/FW target interface](../../../problems/prime-line-sums/manuscripts/cutoff2_t75_fw_theta_target_interface.md)
retains a distinct general-character theta/progression argument, including
zero/height, smoothing and proper-prime-power hypotheses. The original
[T75 §T75.6](../../../problems/prime-line-sums/manuscripts/cutoff2_target_below1475.md)
refers to BMOR Propositions 2.1, 2.5, 2.7 and 4.34 at their stated domains; these are
not the finite Theorem 1.9 endpoint estimate above. Formalizing and checking
that separate argument for the selected modulus and actual target intervals,
or supplying another valid classwise prime-progression theorem at this scale,
are potential ways to close the domain gap. This diagnostic does not verify
either route. The currently audited selected T75 Lean interface still takes
prime brackets and controlled-grid supplies as explicit hypotheses.

The exact rational comparison can be reproduced with Python 3.11+:

```sh
python3.11 - <<'PY'
from fractions import Fraction as F
bound = F(19485) * F(243, 500) * (4 * 2**30) * F(1239, 1240)
cutoff = F(4 * 10**13)
print('lower bound:', bound)
print('excess:', bound - cutoff)
assert bound > cutoff
PY
```

Expected output is lower bound `157477266870239232/3875` and excess
`2477266870239232/3875`. This arithmetic does not check the imported analytic
hypotheses or the target-prime construction.
