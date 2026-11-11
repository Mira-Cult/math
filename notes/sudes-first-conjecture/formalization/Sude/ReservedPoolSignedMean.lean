import Sude.ReservedPoolMean

/-! Exact signed mean accounting for the actual physical unused pool.
No bound on a reserved family, occupancy, or completed line is asserted. -/
namespace Sude
noncomputable section

/-- The change in actual unused-pool mean is the negative signed deviation of
the physically reserved entries, divided by the actual unused cardinality. -/
theorem actual_unused_mean_signed_update {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (hpos : 0 < (actualUnusedPool a reserved).card) :
    centralEntriesMean (actualUnusedPool a reserved) centralPoolValue =
      centralEntriesMean (prescribedPoolValues n) centralPoolValue -
        ((∑ z ∈ reserved, (entry a z : ℝ)) -
          (reserved.card : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue) /
          ((actualUnusedPool a reserved).card : ℝ) := by
  classical
  let chosen := reserved.image (entryPool a)
  have hsub : chosen ⊆ prescribedPoolValues n := fun v _ => mem_prescribedPoolValues v
  have heq : (prescribedPoolValues n) \ chosen = actualUnusedPool a reserved :=
    (actualUnusedPool_eq_full_sdiff a reserved).symm
  have hpos' : 0 < ((prescribedPoolValues n) \ chosen).card := by rw [heq]; exact hpos
  have hmean := central_entries_actual_mean_update (prescribedPoolValues n) chosen
    centralPoolValue hsub hpos'
  have hcard : chosen.card = reserved.card :=
    Finset.card_image_of_injective _ (entryPool a).injective
  have hsum : (∑ v ∈ chosen, centralPoolValue v) = ∑ z ∈ reserved, (entry a z : ℝ) := by
    dsimp [chosen]
    rw [Finset.sum_image]
    · rfl
    · intro x _ y _ h
      exact (entryPool a).injective h
  simpa only [heq, hcard, hsum] using hmean

/-- The same exact identity in the source's `T/n²` normalization. -/
theorem actual_unused_mean_signed_update_source {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (hreserved : reserved.card < n * n) :
    centralEntriesMean (actualUnusedPool a reserved) centralPoolValue =
      (Lucas.poolTotal n : ℝ) / (n * n : ℕ) -
        ((∑ z ∈ reserved, (entry a z : ℝ)) -
          (reserved.card : ℝ) * ((Lucas.poolTotal n : ℝ) / (n * n : ℕ))) /
          (n * n - reserved.card : ℕ) := by
  have hpos : 0 < (actualUnusedPool a reserved).card := by
    rw [actualUnusedPool_card_eq_sub]
    omega
  simpa only [prescribedPoolValues_mean, actualUnusedPool_card_eq_sub] using
    actual_unused_mean_signed_update a reserved hpos

end
end Sude
