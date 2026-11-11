import Mathlib.Tactic

/-! Generic real arithmetic for the affine wheel threshold in AW3--AW4.
This does not establish wheel discrepancy, candidate supply, or a trace. -/
namespace Sude
noncomputable section

/-- The fixed phase origin R_* from AW3. -/
def fwAffineOrigin (C r X eta Mf : ℝ) : ℝ := (1 / 2 + C) * r * X / (eta * Mf)
/-- The stage-dependent t_j from AW3, before division by rho. -/
def fwAffineSlope (eta g M r X : ℝ) : ℝ := eta * g * M / (r * X)
/-- The source real gap threshold D. -/
def fwAffineThreshold (g rho eta M R r X C : ℝ) : ℝ :=
  (g / rho) * (eta * M * R / (r * X) - (1 / 2 + C))

/-- The exact AW4 decomposition, valid for nonzero denominators. -/
theorem fw_affine_threshold_identity
    {g rho eta M R r X C Mf : ℝ} (hr : r ≠ 0) (hX : X ≠ 0)
    (heta : eta ≠ 0) (hMf : Mf ≠ 0) (hrho : rho ≠ 0) :
    fwAffineThreshold g rho eta M R r X C =
      (fwAffineSlope eta g M r X / rho) * (R - fwAffineOrigin C r X eta Mf) +
        (g * (1 / 2 + C) / rho) * (M / Mf - 1) := by
  unfold fwAffineThreshold fwAffineSlope fwAffineOrigin
  field_simp; ring

/-- Under the source's positive inputs, nonnegative discrepancy allowance,
stock lower bound, positive shifted radius and slope cap, AW4 holds. -/
theorem fw_affine_threshold_bounds
    {g rho eta M R r X C Mf : ℝ}
    (hg : 0 < g) (hrho : 0 < rho) (heta : 0 < eta) (hr : 0 < r)
    (hX : 0 < X) (hC : 0 ≤ C) (hMf : 0 < Mf) (hM : Mf ≤ M)
    (hS : 0 < R - fwAffineOrigin C r X eta Mf)
    (hslope : fwAffineSlope eta g M r X / rho ≤ 1) :
    0 < fwAffineThreshold g rho eta M R r X C ∧
      fwAffineThreshold g rho eta M R r X C ≤ R ∧
      (fwAffineSlope eta g M r X / rho) * (R - fwAffineOrigin C r X eta Mf) ≤
        fwAffineThreshold g rho eta M R r X C := by
  have hMpos : 0 < M := hMf.trans_le hM
  have hA : 0 < (1 / 2 : ℝ) + C := by linarith
  have hO : 0 < fwAffineOrigin C r X eta Mf := by
    unfold fwAffineOrigin
    positivity
  have hR : 0 < R := by linarith
  have hK : 0 < fwAffineSlope eta g M r X / rho := by
    unfold fwAffineSlope
    positivity
  have hratio : 0 ≤ M / Mf - 1 := by
    have := (one_le_div hMf).2 hM
    linarith
  have hterm : 0 ≤ (g * (1 / 2 + C) / rho) * (M / Mf - 1) := by positivity
  have hid := fw_affine_threshold_identity (g := g) (rho := rho) (eta := eta) (M := M)
    (R := R) (r := r) (X := X) (C := C) (Mf := Mf)
    (ne_of_gt hr) (ne_of_gt hX) (ne_of_gt heta) (ne_of_gt hMf) (ne_of_gt hrho)
  have hlo : (fwAffineSlope eta g M r X / rho) * (R - fwAffineOrigin C r X eta Mf) ≤
      fwAffineThreshold g rho eta M R r X C := by rw [hid]; linarith
  have hfirst : 0 < fwAffineThreshold g rho eta M R r X C :=
    lt_of_lt_of_le (mul_pos hK hS) hlo
  have hupper0 : fwAffineThreshold g rho eta M R r X C ≤
      (fwAffineSlope eta g M r X / rho) * R := by
    unfold fwAffineThreshold fwAffineSlope
    have hG : 0 ≤ g / rho := le_of_lt (div_pos hg hrho)
    have hga : 0 ≤ (g / rho) * (1 / 2 + C) := mul_nonneg hG hA.le
    have hid' : (g / rho) * (eta * M * R / (r * X)) =
        (eta * g * M / (r * X) / rho) * R := by ring
    nlinarith
  have hupper : (fwAffineSlope eta g M r X / rho) * R ≤ R := by
    nlinarith
  exact ⟨hfirst, hupper0.trans hupper, hlo⟩

end
end Sude
