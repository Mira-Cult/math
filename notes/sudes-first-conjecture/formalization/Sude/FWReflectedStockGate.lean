import Sude.FWReflectedGeometry
import Sude.BMORMidpointGate

/-! One midpoint-error stock gate for all actual FW reflected bins. -/
namespace Sude
noncomputable section

/-- Every FW reflected bin has the exact source width, and every upper
endpoint is bounded by the source's uniform mean-based envelope. -/
theorem fw_reflected_bin_width_upper (m X : ℝ) (hX : 100 ≤ X)
    (hmhi : m ≤ (123 / 250 : ℝ) * X) :
    ∀ z, fwReflectedRight m X z - fwReflectedLeft m X z = (2 / 235 : ℝ) * X ∧
      fwReflectedRight m X z ≤
        ((123 / 250 : ℝ) + ((16 / 235 : ℝ) + 1 / 3) + 16 / 235) * X := by
  rintro ⟨i, side⟩
  have hi : ((i.val : ℝ) + 1) ≤ 16 := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  have hstep : 0 ≤ (2 / 235 : ℝ) * X := by positivity
  have hiT := mul_le_mul_of_nonneg_right hi hstep
  have hi0 : 0 ≤ (i.val : ℝ) * ((2 / 235 : ℝ) * X) := by positivity
  cases side <;> simp only [fwReflectedLeft, fwReflectedRight, reflectedBinLeft,
    reflectedBinRight, fwReflectedLowAnchor, fwReflectedHighAnchor, fwReflectedStep,
    Bool.false_eq_true, ↓reduceIte] <;> constructor
  all_goals try ring
  all_goals nlinarith

/-- One explicit midpoint-error lower bound suffices for every FW bin's
exact BMOR endpoint gate. The scalar bound itself is an internal numerical
obligation. -/
theorem fw_reflected_uniform_endpoint_gate (m X : ℝ) (W : ℕ)
    (hX : 100 ≤ X) (hmlo : (243 / 500 : ℝ) * X ≤ m)
    (hmhi : m ≤ (123 / 250 : ℝ) * X)
    (hW : (W : ℝ) ≤
      ((2 / 235 : ℝ) * X - 2 * (518 / 125 : ℝ) *
        Real.sqrt (((123 / 250 : ℝ) + ((16 / 235 : ℝ) + 1 / 3) + 16 / 235) * X)) /
          Real.log X) :
    ∀ z, (W : ℝ) ≤
      ((fwReflectedRight m X z - fwReflectedLeft m X z) -
        (518 / 125 : ℝ) * (Real.sqrt (fwReflectedLeft m X z) +
          Real.sqrt (fwReflectedRight m X z))) / Real.log X := by
  intro z
  have hgeo := fw_reflected_bin_geometry m X hX hmlo hmhi
  have hw := fw_reflected_bin_width_upper m X hX hmhi z
  have hleft : 0 ≤ fwReflectedLeft m X z := by linarith [(hgeo.1 z).1]
  have hright : 0 ≤ fwReflectedRight m X z := by linarith [(hgeo.1 z).1, (hgeo.1 z).2.1]
  have hmid : (fwReflectedLeft m X z + fwReflectedRight m X z) / 2 ≤
      ((123 / 250 : ℝ) + ((16 / 235 : ℝ) + 1 / 3) + 16 / 235) * X := by
    linarith [(hgeo.1 z).2.1, hw.2]
  apply bmor_endpoint_gate_of_midpoint _ _ _ X W hleft hright hmid (by linarith)
  simpa only [hw.1] using hW

end
end Sude
