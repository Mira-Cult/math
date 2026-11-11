import Sude.DiagonalFullStockSelection
import Sude.ActualUnusedPool

/-! Place the two DQ full-stock batches into supplied free cells, after any
center handling. Later line estimates and exceptional stock remain separate. -/
namespace Sude
noncomputable section

/-- Install successive full-stock selections into disjoint free-cell sets,
preserve the entire supplied reservation, and identify the exact remaining
prescribed pool. The two sets can be the remaining main and antidiagonal cells
after their common center is already handled. -/
theorem actual_unused_pool_place_two_batches {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved Y Z : Finset (Cell n))
    (hYR : Disjoint Y reserved) (hZR : Disjoint Z reserved) (hYZ : Disjoint Y Z)
    (hroom : Y.card + Z.card < (actualUnusedPool a reserved).card) :
    ∃ (b : Cell n ≃ Fin (n * n)) (T U : Finset (pool n)),
      T ⊆ actualUnusedPool a reserved ∧ U ⊆ actualUnusedPool a reserved \ T ∧
      T.card = Y.card ∧ U.card = Z.card ∧
      Y.image (entry b) = T.image Subtype.val ∧ Z.image (entry b) = U.image Subtype.val ∧
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      actualUnusedPool b (reserved ∪ (Y ∪ Z)) = (actualUnusedPool a reserved \ T) \ U ∧
      0 < (actualUnusedPool b (reserved ∪ (Y ∪ Z))).card ∧
      |(∑ z ∈ Y, (entry b z : ℝ)) - (Y.card : ℝ) *
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤ (poolMaximum n : ℝ) / 2 ∧
      |(∑ z ∈ Z, (entry b z : ℝ)) - (Z.card : ℝ) *
        centralEntriesMean (actualUnusedPool a reserved \ T) centralPoolValue| ≤ (poolMaximum n : ℝ) / 2 ∧
      |(∑ z ∈ Y ∪ Z, (entry b z : ℝ)) - ((Y.card + Z.card : ℕ) : ℝ) *
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤ (poolMaximum n : ℝ) := by
  classical
  obtain ⟨T, U, hT, hU, hTc, hUc, hfirst, hsecond, hpos, hsum⟩ :=
    actual_unused_pool_two_batches a reserved Y.card Z.card hroom
  have hTU : Disjoint T U := by
    apply Finset.disjoint_left.mpr
    intro x hx hxU
    exact (Finset.mem_sdiff.mp (hU hxU)).2 hx
  have havoid : ∀ v ∈ (∅ : Finset (pool n)) ∪ T ∪ U, ∀ z ∈ reserved, v.val ≠ entry a z := by
    intro v hv z hz
    have hv' : v ∈ actualUnusedPool a reserved := by
      simp only [Finset.empty_union, Finset.mem_union] at hv
      rcases hv with hv | hv
      · exact hT hv
      · exact (Finset.mem_sdiff.mp (hU hv)).1
    exact actualUnusedPool_avoids a reserved v hv' z hz
  obtain ⟨b, _, hY, hZ, hfixed, _, _⟩ :=
    place_three_finite_populations a ∅ Y Z ∅ T U reserved (by simp) hTc hUc
      (by simp) hYR hZR (by simp) (by simp) hYZ (by simp) (by simp) hTU havoid
  have himage : (Y ∪ Z).image (entry b) = (T ∪ U).image Subtype.val := by
    rw [Finset.image_union, hY, hZ, Finset.image_union]
  have hleft := actualUnusedPool_after_placement a b reserved (Y ∪ Z) (T ∪ U) hfixed himage
  have hdiff : actualUnusedPool a reserved \ (T ∪ U) = (actualUnusedPool a reserved \ T) \ U := by
    ext v
    simp [and_assoc, and_comm, and_left_comm]
  rw [hdiff] at hleft
  have hsumY := finite_population_sum b Y T hY
  have hsumZ := finite_population_sum b Z U hZ
  have hsumYZ := finite_population_sum b (Y ∪ Z) (T ∪ U) himage
  exact ⟨b, T, U, hT, hU, hTc, hUc, hY, hZ, hfixed, hleft, hleft ▸ hpos,
    by simpa [hsumY] using hfirst, by simpa [hsumZ] using hsecond,
    by simpa [hsumYZ] using hsum⟩

end
end Sude
