import Sude.FWPrefixMidpointPoolBound
import Sude.FWThetaInputs

/-! Physical pair midpoint bounds for arbitrary supplied stages.

The placement and stage cells are supplied; no injection, growth trace,
rectangle allowance, or full-line estimate is asserted. The theta and RS
estimates are explicit hypotheses in the final corollaries. -/
namespace Sude
noncomputable section

/-- A physical entry is in the prescribed pool interval. -/
theorem physical_entry_pool_range {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (c : Cell n) : 0 ≤ (entry a c : ℝ) ∧ (entry a c : ℝ) ≤ poolMaximum n := by
  have hp : entry a c ∈ pool n := by
    rw [← entry_range a]
    exact ⟨c, rfl⟩
  constructor
  · exact Nat.cast_nonneg _
  · exact_mod_cast pool_le_poolMaximum hp

/-- The midpoint of any two physical entries lies in the pool interval. -/
theorem physical_pair_midpoint_pool_range {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (c d : Cell n) :
    0 ≤ ((entry a c : ℝ) + entry a d) / 2 ∧
      ((entry a c : ℝ) + entry a d) / 2 ≤ poolMaximum n := by
  have hc := physical_entry_pool_range a c
  have hd := physical_entry_pool_range a d
  constructor <;> linarith

/-- Any nonempty supplied physical stage has the bound whenever the actual
pool mean satisfies the stated enclosure. Cells need not be distinct. -/
theorem fw_physical_stage_mean_pool_bound {n Q : ℕ} (hQ : 0 < Q)
    (a : Cell n ≃ Fin (n * n)) (cells : Fin Q → Bool → Cell n)
    (hμlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤
      (Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ))
    (hμhi : (Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ) ≤
      (123 / 250 : ℝ) * (poolMaximum n : ℝ)) :
    |(∑ i, ((entry a (cells i false) : ℝ) + entry a (cells i true)) / 2) / (Q : ℝ) -
      (Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ)| ≤
        (257 / 500 : ℝ) * (poolMaximum n : ℝ) := by
  apply fw_prefix_stage_mean_pool_bound hQ _ _ _ (Nat.cast_nonneg _) hμlo hμhi
  intro i
  exact physical_pair_midpoint_pool_range a (cells i false) (cells i true)

/-- The enclosure follows from the explicit finite-theta and RS hypotheses on
the FW order interval; it is not proved unconditionally here. -/
theorem fw_physical_stage_mean_pool_bound_of_theta
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n Q : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hQ : 0 < Q)
    (a : Cell n ≃ Fin (n * n)) (cells : Fin Q → Bool → Cell n) :
    |(∑ i, ((entry a (cells i false) : ℝ) + entry a (cells i true)) / 2) / (Q : ℝ) -
      (Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ)| ≤
        (257 / 500 : ℝ) * (poolMaximum n : ℝ) := by
  obtain ⟨hlo, hhi⟩ := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo hnhi
  exact fw_physical_stage_mean_pool_bound hQ a cells hlo hhi

/-- Any finite set of supplied physical stage means has the triangle bound.
No claim is made about a growth construction or line budgets. -/
theorem fw_physical_stage_means_sum_pool_bound_of_theta {I : Type*}
    (stages : Finset I) (bmor : BMORFiniteTheta) (lower : RSIndexLower)
    (upper : RSIndexUpper) {n Q : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hQ : 0 < Q) (a : Cell n ≃ Fin (n * n))
    (cells : (I × Fin Q) × Bool → Cell n) :
    |∑ j ∈ stages, ((∑ i, ((entry a (cells ((j, i), false)) : ℝ) +
      entry a (cells ((j, i), true))) / 2) / (Q : ℝ) -
      (Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ))| ≤
        (stages.card : ℝ) * ((257 / 500 : ℝ) * (poolMaximum n : ℝ)) := by
  obtain ⟨hlo, hhi⟩ := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo hnhi
  apply fw_prefix_stage_means_sum_pool_bound stages hQ _ _ _ (Nat.cast_nonneg _) hlo hhi
  intro j _ i
  exact physical_pair_midpoint_pool_range a (cells ((j, i), false)) (cells ((j, i), true))

end
end Sude
