import Sude.BMORMidpointError

/-! Translate a midpoint-error stock bound to the exact endpoint gate. -/
namespace Sude
noncomputable section

/-- An explicit midpoint stock bound implies the exact two-endpoint BMOR
stock hypothesis. The logarithm's sign and all endpoint domains are stated. -/
theorem bmor_endpoint_gate_of_midpoint (b c M X : ℝ) (W : ℕ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hM : (b + c) / 2 ≤ M) (hX : 1 ≤ X)
    (hW : (W : ℝ) ≤ ((c - b) - 2 * (518 / 125 : ℝ) * Real.sqrt M) / Real.log X) :
    (W : ℝ) ≤ ((c - b) - (518 / 125 : ℝ) * (Real.sqrt b + Real.sqrt c)) / Real.log X := by
  have hs := sqrt_endpoints_le_two_midpoint b c hb hc
  have hm := Real.sqrt_le_sqrt hM
  have hnum : (c - b) - 2 * (518 / 125 : ℝ) * Real.sqrt M ≤
      (c - b) - (518 / 125 : ℝ) * (Real.sqrt b + Real.sqrt c) := by linarith
  exact hW.trans (div_le_div_of_nonneg_right hnum (Real.log_nonneg hX))

end
end Sude
