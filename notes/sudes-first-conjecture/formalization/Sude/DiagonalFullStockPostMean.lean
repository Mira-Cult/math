import Sude.DiagonalFullStockCenterBatches
import Sude.DiagonalFullStockMean
namespace Sude
noncomputable section

/-- Recover the exact chosen center value and post-center pool from the
same physical witness, then bound its mean shift. -/
theorem actual_center_recovered_mean_shift {n : ℕ} (a b₀ : Cell n ≃ Fin (n*n))
    (reserved : Finset (Cell n)) (center : Cell n) (hcenter : center ∉ reserved)
    (hfixed : ∀ z ∈ reserved, entry b₀ z = entry a z)
    (hpos : 0 < (actualUnusedPool b₀ (reserved ∪ {center})).card)
    (hexpect : ∀ line : Finset (Cell n),
        |((∑ z ∈ line ∩ (reserved ∪ {center}), (entry b₀ z : ℝ)) +
            ((line \ (reserved ∪ {center})).card : ℝ) *
              centralEntriesMean (actualUnusedPool b₀ (reserved ∪ {center})) centralPoolValue) -
          ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
            ((line \ reserved).card : ℝ) *
              centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (poolMaximum n : ℝ) / 2) :
    let T : Finset (pool n) := {entryPool b₀ center}
    T ⊆ actualUnusedPool a reserved ∧
    actualUnusedPool b₀ (reserved ∪ {center}) = actualUnusedPool a reserved \ T ∧
    |(entry b₀ center : ℝ) - centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
      (poolMaximum n : ℝ) / 2 ∧
    |centralEntriesMean (actualUnusedPool b₀ (reserved ∪ {center})) centralPoolValue -
      centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
      (poolMaximum n : ℝ) / (2 * (actualUnusedPool b₀ (reserved ∪ {center})).card) := by
  classical
  let T : Finset (pool n) := {entryPool b₀ center}
  have hT : T ⊆ actualUnusedPool a reserved := by
    intro v hv
    have hv' : v = entryPool b₀ center := by simpa [T] using hv
    subst v
    apply (mem_actualUnusedPool a reserved (entryPool b₀ center)).2
    intro z hz heq
    have hb : entry b₀ center = entry b₀ z := by simpa [hfixed z hz] using heq
    have he := entry_injective b₀ hb
    exact hcenter (he ▸ hz)
  have himage : ({center} : Finset (Cell n)).image (entry b₀) = T.image Subtype.val := by
    simp [T]
  have hremain := actualUnusedPool_after_placement a b₀ reserved {center} T hfixed himage
  have hnear : |(entry b₀ center : ℝ) - centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
      (poolMaximum n : ℝ) / 2 := by
    have hi : ({center} : Finset (Cell n)) \ (reserved ∪ {center}) = ∅ := by
      apply Finset.sdiff_eq_empty_iff_subset.mpr
      intro z hz
      exact Finset.mem_union_right _ hz
    have hj : ({center} : Finset (Cell n)) \ reserved = {center} := by
      apply Finset.sdiff_eq_self_iff_disjoint.mpr
      simpa using hcenter
    have h := hexpect {center}
    rw [hi, hj] at h
    simpa [hcenter] using h
  have hpos' : 0 < (actualUnusedPool a reserved \ T).card := by rw [← hremain]; exact hpos
  have hm := central_entries_actual_mean_update (actualUnusedPool a reserved) T centralPoolValue hT hpos'
  have hcard : T.card = 1 := by simp [T]
  have hsum : (∑ v ∈ T, centralPoolValue v) = (entry b₀ center : ℝ) := by simp [T, centralPoolValue]
  rw [hsum, hcard] at hm
  simp only [Nat.cast_one, one_mul] at hm
  have hden : (0 : ℝ) < (actualUnusedPool b₀ (reserved ∪ {center})).card := by exact_mod_cast hpos
  have hshift : |centralEntriesMean (actualUnusedPool b₀ (reserved ∪ {center})) centralPoolValue -
      centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
      (poolMaximum n : ℝ) / (2 * (actualUnusedPool b₀ (reserved ∪ {center})).card) := by
    rw [hremain, hm]
    have heq : centralEntriesMean (actualUnusedPool a reserved) centralPoolValue -
          ((entry b₀ center : ℝ) - centralEntriesMean (actualUnusedPool a reserved) centralPoolValue) /
            ((actualUnusedPool a reserved \ T).card : ℝ) - centralEntriesMean (actualUnusedPool a reserved) centralPoolValue =
        -(((entry b₀ center : ℝ) - centralEntriesMean (actualUnusedPool a reserved) centralPoolValue) /
            ((actualUnusedPool a reserved \ T).card : ℝ)) := by ring
    have hden' : (0 : ℝ) < (actualUnusedPool a reserved \ T).card := by exact_mod_cast hpos'
    rw [heq, abs_neg, abs_div, abs_of_pos hden']
    have h := div_le_div_of_nonneg_right hnear hden'.le
    simpa [div_div] using h
  exact ⟨hT, hremain, hnear, hshift⟩
/-- On the same center and batch witnesses, combine the two exact mean
updates. The denominator in each term is the actual pool at that stage. -/
theorem center_and_batches_post_mean_shift {n : ℕ}
    (a b₀ b : Cell n ≃ Fin (n * n)) (reserved Y Z : Finset (Cell n))
    (center : Cell n) (T U : Finset (pool n)) (hcenter : center ∉ reserved)
    (hfixed₀ : ∀ z ∈ reserved, entry b₀ z = entry a z)
    (hexpect : ∀ line : Finset (Cell n),
        |((∑ z ∈ line ∩ (reserved ∪ {center}), (entry b₀ z : ℝ)) +
            ((line \ (reserved ∪ {center})).card : ℝ) *
              centralEntriesMean (actualUnusedPool b₀ (reserved ∪ {center})) centralPoolValue) -
          ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
            ((line \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (poolMaximum n : ℝ) / 2)
    (hT : T ⊆ actualUnusedPool b₀ (reserved ∪ {center}))
    (hU : U ⊆ actualUnusedPool b₀ (reserved ∪ {center}) \ T)
    (hTc : T.card = Y.card) (hUc : U.card = Z.card)
    (hY : Y.image (entry b) = T.image Subtype.val)
    (hZ : Z.image (entry b) = U.image Subtype.val)
    (hremain : actualUnusedPool b ((reserved ∪ {center}) ∪ (Y ∪ Z)) =
      (actualUnusedPool b₀ (reserved ∪ {center}) \ T) \ U)
    (hpos : 0 < (actualUnusedPool b ((reserved ∪ {center}) ∪ (Y ∪ Z))).card)
    (hsum : |(∑ z ∈ Y ∪ Z, (entry b z : ℝ)) - ((Y.card + Z.card : ℕ) : ℝ) *
      centralEntriesMean (actualUnusedPool b₀ (reserved ∪ {center})) centralPoolValue| ≤ (poolMaximum n : ℝ)) :
    |centralEntriesMean (actualUnusedPool b ((reserved ∪ {center}) ∪ (Y ∪ Z))) centralPoolValue -
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
      (poolMaximum n : ℝ) / (2 * (actualUnusedPool b₀ (reserved ∪ {center})).card) +
        (poolMaximum n : ℝ) / (actualUnusedPool b ((reserved ∪ {center}) ∪ (Y ∪ Z))).card := by
  have hsub : (actualUnusedPool b₀ (reserved ∪ {center}) \ T) \ U ⊆
      actualUnusedPool b₀ (reserved ∪ {center}) := Finset.sdiff_subset.trans Finset.sdiff_subset
  have hc := Finset.card_le_card hsub
  rw [← hremain] at hc
  have hpos₀ : 0 < (actualUnusedPool b₀ (reserved ∪ {center})).card := by omega
  have hcenterShift := (actual_center_recovered_mean_shift a b₀ reserved center hcenter hfixed₀ hpos₀ hexpect).2.2.2
  have hbatch := (placed_full_stock_mean_and_width b₀ b (reserved ∪ {center}) Y Z T U
    hT hU hTc hUc hY hZ hremain hpos hsum).1
  have htriangle := abs_sub_le
    (centralEntriesMean (actualUnusedPool b ((reserved ∪ {center}) ∪ (Y ∪ Z))) centralPoolValue)
    (centralEntriesMean (actualUnusedPool b₀ (reserved ∪ {center})) centralPoolValue)
    (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)
  linarith

end
end Sude
