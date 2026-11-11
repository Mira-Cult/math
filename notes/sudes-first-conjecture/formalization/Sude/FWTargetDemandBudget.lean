import Sude.FWFirstBandWideCapacity
import Sude.FWReferencePrimeTargets

/-! Numeric rounding and triangle-inequality interfaces for first-band target
demands. These do not construct targets or bound the actual reference lines. -/
namespace Sude
noncomputable section

/-- The integer demand box pays the FW18 factor 0.999 * (519 / 500), once
the capacity is at least 3000. Both floors are included in the estimate. -/
theorem fw_demand_box_rounding {N : ℕ} (hN : 3000 ≤ N) :
    500 * (519 * (N / 2) / 500) ≤ 519 * (N / 2) ∧
    518481 * N ≤ 1000000 * (519 * (N / 2) / 500) := by
  have h₂ := Nat.mod_add_div N 2
  have h₂lt : N % 2 < 2 := Nat.mod_lt _ (by decide)
  have h₅₀₀ := Nat.mod_add_div (519 * (N / 2)) 500
  have h₅₀₀lt : (519 * (N / 2)) % 500 < 500 := Nat.mod_lt _ (by decide)
  omega

/-- The Rosser–Schoenfeld pool bound supplies the rounding threshold in the
first FW band. -/
theorem fw_first_band_demand_rounding_threshold (lower : RSIndexLower) {n : ℕ}
    (hn : 19485 ≤ n) : 3000 ≤ (n / 450) * poolMaximum n := by
  have hk : 1 ≤ n / 450 := by omega
  have hx : 3000 ≤ poolMaximum n := by
    have h := fw_poolMaximum_gt_four_seed lower hn
    norm_num at h
    omega
  nlinarith

/-- A target and a baseline close to the same real center are close to each
other. The hypotheses are deliberately about the supplied baseline. -/
theorem fw_target_baseline_triangle {target baseline B : ℕ} {μ U D : ℝ}
    (hbase : |(baseline : ℝ) - μ| ≤ U)
    (htarget : |(target : ℝ) - μ| ≤ D)
    (hbudget : U + D ≤ 2 * (B : ℝ)) :
    |(target : ℤ) - baseline| ≤ (2 : ℤ) * B := by
  have htriangle : |(target : ℝ) - baseline| ≤ U + D := by
    calc
      |(target : ℝ) - baseline| = |((target : ℝ) - μ) + (μ - baseline)| := by congr 1; ring
      _ ≤ |(target : ℝ) - μ| + |μ - (baseline : ℝ)| := abs_add_le _ _
      _ ≤ U + D := by rw [abs_sub_comm μ (baseline : ℝ)]; linarith
  have hreal : |(target : ℝ) - baseline| ≤ 2 * (B : ℝ) := htriangle.trans hbudget
  exact_mod_cast hreal

/-- FW18's unrounded numerical budget implies the integer demand bound for
the particular baseline and target for which the two estimates are supplied. -/
theorem fw_target_baseline_of_fw18 {target baseline N : ℕ} {μ U D : ℝ}
    (hN : 3000 ≤ N)
    (hbase : |(baseline : ℝ) - μ| ≤ U)
    (htarget : |(target : ℝ) - μ| ≤ D)
    (hbudget : U + D ≤ (518481 / 500000 : ℝ) * N) :
    |(target : ℤ) - baseline| ≤ (2 : ℤ) * (519 * (N / 2) / 500 : ℕ) := by
  have hnat := (fw_demand_box_rounding hN).2
  have hreal : (518481 : ℝ) * N ≤ 1000000 * (519 * (N / 2) / 500 : ℕ) := by
    exact_mod_cast hnat
  apply fw_target_baseline_triangle hbase htarget
  nlinarith

/-- Apply the triangle estimate to both line families of the same reference
square. None of the prime, total, diagonal, or line estimates is inferred. -/
theorem fw_reference_target_bounds_of_fw18 {n N : ℕ}
    (b₀ : Cell n ≃ Fin (n * n)) (rowTarget colTarget : Fin n → ℕ)
    {μ U D : ℝ} (hN : 3000 ≤ N)
    (hrowBase : ∀ i, |(rowSum b₀ i : ℝ) - μ| ≤ U)
    (hcolBase : ∀ i, |(columnSum b₀ i : ℝ) - μ| ≤ U)
    (hrowTarget : ∀ i, |(rowTarget i : ℝ) - μ| ≤ D)
    (hcolTarget : ∀ i, |(colTarget i : ℝ) - μ| ≤ D)
    (hbudget : U + D ≤ (518481 / 500000 : ℝ) * N) :
    (∀ i, |(rowTarget i : ℤ) - rowSum b₀ i| ≤
      (2 : ℤ) * (519 * (N / 2) / 500 : ℕ)) ∧
    (∀ i, |(colTarget i : ℤ) - columnSum b₀ i| ≤
      (2 : ℤ) * (519 * (N / 2) / 500 : ℕ)) := by
  exact ⟨fun i => fw_target_baseline_of_fw18 hN (hrowBase i) (hrowTarget i) hbudget,
    fun i => fw_target_baseline_of_fw18 hN (hcolBase i) (hcolTarget i) hbudget⟩

end
end Sude
