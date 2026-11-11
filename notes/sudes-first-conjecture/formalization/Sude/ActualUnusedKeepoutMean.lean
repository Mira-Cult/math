import Sude.ActualUnusedKeepoutDifference
import Sude.CentralStock

/-! Exact mean update when additional physical keepout cells are reserved.
No numerical mean or value bound is asserted. -/
namespace Sude
noncomputable section

/-- The mean of the full-keepout unused pool equals the role-relative mean
minus the centered contribution of the actual entries in the additional
keepout cells, divided by the positive full-keepout unused count. -/
theorem actualUnusedPool_full_mean_eq_roles_mean_sub_extra {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (roles full : Finset (Cell n))
    (hsub : roles ⊆ full) (hpos : 0 < (actualUnusedPool a full).card) :
    centralEntriesMean (actualUnusedPool a full) (fun v : pool n => (v.val : ℝ)) =
      centralEntriesMean (actualUnusedPool a roles) (fun v : pool n => (v.val : ℝ)) -
        ((∑ c ∈ full \ roles, (entry a c : ℝ)) -
          ((full \ roles).card : ℝ) *
            centralEntriesMean (actualUnusedPool a roles) (fun v : pool n => (v.val : ℝ))) /
        ((actualUnusedPool a full).card : ℝ) := by
  classical
  let extra := (full \ roles).image (entryPool a)
  have hsubset : extra ⊆ actualUnusedPool a roles := by
    dsimp [extra, actualUnusedPool]
    apply Finset.image_subset_image
    intro c hc
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hc).2⟩
  have hfull : actualUnusedPool a full = actualUnusedPool a roles \ extra :=
    actualUnusedPool_full_eq_roles_sdiff a roles full hsub
  have hpos' : 0 < (actualUnusedPool a roles \ extra).card := by
    rw [← hfull]
    exact hpos
  have hsum : (∑ v ∈ extra, (v.val : ℝ)) = ∑ c ∈ full \ roles, (entry a c : ℝ) := by
    dsimp [extra]
    rw [Finset.sum_image (by intro x hx y hy h; exact (entryPool a).injective h)]
    simp only [entryPool_val]
  have hcard : extra.card = (full \ roles).card := by
    dsimp [extra]
    exact Finset.card_image_of_injective _ (entryPool a).injective
  have hmean := central_entries_actual_mean_update (actualUnusedPool a roles) extra
    (fun v : pool n => (v.val : ℝ)) hsubset hpos'
  rw [← hfull, hsum, hcard] at hmean
  exact hmean

end
end Sude
