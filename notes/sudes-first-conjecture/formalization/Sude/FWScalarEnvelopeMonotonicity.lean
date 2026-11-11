import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Scalar algebra for the explicit four-family cancellation envelope.
This contains no physical, comparison-budget, or line-bound conclusion. -/
namespace Sude
noncomputable section

/-- The four-family stage-deviation coefficient. -/
def fwScalarEnvelopeA (K P : ℝ) : ℝ :=
  5 * (6109 / 231000) + (16 + P) * (257 / 500) + 3 * K * (1 / 235)

/-- The active-role line occupancy parameter. -/
def fwScalarEnvelopeR (K P : ℝ) : ℝ := 12 * (21 + 3 * K + P)

/-- The number of spare rectangle corners in the scalar model. -/
def fwScalarEnvelopeB (P : ℝ) : ℝ := 96 * (238 - P)

/-- The full-unused denominator in the scalar model. -/
def fwScalarEnvelopeN (n K P : ℝ) : ℝ :=
  n ^ 2 - fwScalarEnvelopeR K P * (n + 8) - fwScalarEnvelopeB P

/-- The signed-cancellation envelope numerator. -/
def fwScalarEnvelopeT (n K P : ℝ) : ℝ :=
  12 * fwScalarEnvelopeA K P * (8 * n + fwScalarEnvelopeB P) +
    (n - fwScalarEnvelopeR K P) * (257 / 500) * fwScalarEnvelopeB P

/-- The numerator is affine in `P` with strictly positive slope, the
positive denominator decreases with `P`, and the ratio is bounded by its
`P = 238` endpoint under the explicit scalar domain assumptions. -/
theorem fw_scalar_envelope_monotone_in_P (n K P : ℝ)
    (hn : 0 ≤ n) (hK : 0 ≤ K) (_hP : 0 ≤ P) (hPmax : P ≤ 238)
    (hNend : 0 < fwScalarEnvelopeN n K 238) :
    let Aend := fwScalarEnvelopeA K 238
    let H : ℝ := 5 * ((257 / 500 : ℝ) - 6109 / 231000) + 3 * K * ((257 / 500 : ℝ) - 1 / 235)
    0 < H ∧
    fwScalarEnvelopeT n K P = 96 * n * Aend - 1152 * H * (238 - P) ∧
    fwScalarEnvelopeN n K P = fwScalarEnvelopeN n K 238 + 12 * n * (238 - P) ∧
    0 < fwScalarEnvelopeN n K P ∧
    fwScalarEnvelopeT n K P / fwScalarEnvelopeN n K P ≤
      fwScalarEnvelopeT n K 238 / fwScalarEnvelopeN n K 238 := by
  dsimp only
  let Aend := fwScalarEnvelopeA K 238
  let H : ℝ := 5 * ((257 / 500 : ℝ) - 6109 / 231000) + 3 * K * ((257 / 500 : ℝ) - 1 / 235)
  have hH : 0 < H := by dsimp [H]; nlinarith
  have hA : 0 ≤ Aend := by dsimp [Aend, fwScalarEnvelopeA]; positivity
  have hT : fwScalarEnvelopeT n K P = 96 * n * Aend - 1152 * H * (238 - P) := by
    dsimp [fwScalarEnvelopeT, fwScalarEnvelopeR, fwScalarEnvelopeB, fwScalarEnvelopeA, Aend, H]
    ring
  have hN : fwScalarEnvelopeN n K P = fwScalarEnvelopeN n K 238 + 12 * n * (238 - P) := by
    dsimp [fwScalarEnvelopeN, fwScalarEnvelopeR, fwScalarEnvelopeB]
    ring
  have hTe : fwScalarEnvelopeT n K 238 = 96 * n * Aend := by
    dsimp [fwScalarEnvelopeT, fwScalarEnvelopeR, fwScalarEnvelopeB, fwScalarEnvelopeA, Aend]
    ring
  have ht : 0 ≤ 238 - P := by linarith
  have hNle : fwScalarEnvelopeN n K 238 ≤ fwScalarEnvelopeN n K P := by
    rw [hN]
    nlinarith [mul_nonneg hn ht]
  have hNpos : 0 < fwScalarEnvelopeN n K P := lt_of_lt_of_le hNend hNle
  have hTle : fwScalarEnvelopeT n K P ≤ 96 * n * Aend := by
    rw [hT]
    have hprod : 0 ≤ 1152 * H * (238 - P) := by positivity
    linarith
  have hnumer : 0 ≤ 96 * n * Aend := by positivity
  refine ⟨hH, hT, hN, hNpos, ?_⟩
  rw [hTe]
  calc
    _ ≤ (96 * n * Aend) / fwScalarEnvelopeN n K P := div_le_div_of_nonneg_right hTle hNpos.le
    _ ≤ (96 * n * Aend) / fwScalarEnvelopeN n K 238 :=
      div_le_div_of_nonneg_left hnumer hNend hNle

end
end Sude
