import Sude.FWBridgeCommonSeed

/-! Source-wide FW rectangle arithmetic, conditional on the growth-stage cap.
See `problems/prime-line-sums/manuscripts/cutoff2_controller_far_wide.md`
FW4--FW5, in particular FW14--FW15, and `cutoff2_rectangle_packing.md` RP1.
No growth trace or validity of its stage cap is asserted here. -/
namespace Sude
noncomputable section

/-- Actual joint rectangle count: 24 per prefix, bridge, or wide stage. -/
def fwJointRectangleCount (n P₀ : ℕ) : ℕ :=
  24 * (P₀ + 5 + 3 * (n / 450))

/-- Integer form of the source FW15 budget with `d=6`, `J=5`, `C=450`.
Here `P` is a supplied cap for the actual prefix stage count. -/
def fwRectangleStageBudget (n P : ℕ) : Prop :=
  450 * (48 * (P + 5) + 16) + 144 * n < 450 * n

/-- The explicit real FW15 inequality implies the equivalent integer budget. -/
theorem fw_rectangle_stage_budget_of_fw15 {n P : ℕ} (hn : 0 < n)
    (hfw15 : (48 : ℝ) * ((P : ℝ) + 5) / n + 144 / 450 + 16 / n < 1) :
    fwRectangleStageBudget n P := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul := mul_lt_mul_of_pos_right hfw15 hnpos
  have hid : ((48 : ℝ) * ((P : ℝ) + 5) / n + 144 / 450 + 16 / n) * n =
      48 * ((P : ℝ) + 5) + 144 * n / 450 + 16 := by
    field_simp
  rw [hid] at hmul
  have hreal : (450 : ℝ) * (48 * ((P : ℝ) + 5) + 16) + 144 * n < 450 * n := by
    nlinarith
  unfold fwRectangleStageBudget
  exact_mod_cast hreal

/-- The actual joint count fits RP1, with 15 cells of additional slack, whenever
the supplied prefix cap satisfies FW15. The floor in the wide-stage count is
retained, and the actual prefix count is required to be no greater than the cap. -/
theorem fw_full_rectangle_capacity {n P₀ P : ℕ} (hP : P₀ ≤ P)
    (hbudget : fwRectangleStageBudget n P) :
    3 ≤ fwJointRectangleCount n P₀ ∧
    5 * (4 * 6) ≤ fwJointRectangleCount n P₀ ∧
    2 * fwJointRectangleCount n P₀ + 16 < n := by
  have hdiv : 450 * (n / 450) ≤ n := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self n 450
  unfold fwRectangleStageBudget at hbudget
  unfold fwJointRectangleCount
  omega

/-- A paid prefix cap of 270 satisfies the FW15 integer budget across the
entire FW order range. This is a conditional arithmetic result, not a proof
that any actual growth trace has that many stages. -/
theorem fw_rectangle_stage_budget_of_cap {n P : ℕ} (hn : 19485 ≤ n)
    (hP : P ≤ 270) : fwRectangleStageBudget n P := by
  unfold fwRectangleStageBudget
  omega

/-- Source-wide RP1 capacity under an explicit actual prefix-stage bound. -/
theorem fw_full_rectangle_capacity_of_cap {n P₀ : ℕ} (hn : 19485 ≤ n)
    (hP₀ : P₀ ≤ 270) :
    3 ≤ fwJointRectangleCount n P₀ ∧
    5 * (4 * 6) ≤ fwJointRectangleCount n P₀ ∧
    2 * fwJointRectangleCount n P₀ + 16 < n :=
  fw_full_rectangle_capacity (le_refl P₀) (fw_rectangle_stage_budget_of_cap hn hP₀)

/-- The concrete early allocation of five bridge and sixteen seed stages fits
throughout the FW range, independently of later growth or wide stages. -/
theorem fw_early_rectangle_capacity {n : ℕ} (hn : 19485 ≤ n) :
    5 * (4 * 6) ≤ 24 * (16 + 5) ∧ 2 * (24 * (16 + 5)) + 1 ≤ n := by
  omega

end
end Sude
