import Sude.DiagonalFullStockPlacement
import Sude.PrefixPopulationMeanWidth

/-! DQ2's actual post-batch mean shift and individual-value bounds. -/
namespace Sude
noncomputable section

/-- For two actually placed batches, the signed combined discrepancy controls
the exact post-placement mean. The old pool is the one from the same source
square, not an independently chosen population. -/
theorem placed_full_stock_mean_and_width {n : ℕ}
    (a b : Cell n ≃ Fin (n * n)) (reserved Y Z : Finset (Cell n))
    (T U : Finset (pool n))
    (hT : T ⊆ actualUnusedPool a reserved)
    (hU : U ⊆ actualUnusedPool a reserved \ T)
    (hTc : T.card = Y.card) (hUc : U.card = Z.card)
    (hY : Y.image (entry b) = T.image Subtype.val)
    (hZ : Z.image (entry b) = U.image Subtype.val)
    (hremain : actualUnusedPool b (reserved ∪ (Y ∪ Z)) =
      (actualUnusedPool a reserved \ T) \ U)
    (hpos : 0 < (actualUnusedPool b (reserved ∪ (Y ∪ Z))).card)
    (hsum : |(∑ z ∈ Y ∪ Z, (entry b z : ℝ)) - ((Y.card + Z.card : ℕ) : ℝ) *
      centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤ (poolMaximum n : ℝ)) :
    |centralEntriesMean (actualUnusedPool b (reserved ∪ (Y ∪ Z))) centralPoolValue -
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
      (poolMaximum n : ℝ) / (actualUnusedPool b (reserved ∪ (Y ∪ Z))).card ∧
    ∀ z ∈ Y ∪ Z, |(entry b z : ℝ) -
      centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤ poolMaximum n := by
  classical
  let stock := actualUnusedPool a reserved
  have hsub : T ∪ U ⊆ stock := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hT hx
    · exact (Finset.mem_sdiff.mp (hU hx)).1
  have hdis : Disjoint T U := by
    apply Finset.disjoint_left.mpr
    intro x hx hu
    exact (Finset.mem_sdiff.mp (hU hu)).2 hx
  have hcard : (T ∪ U).card = Y.card + Z.card := by
    rw [Finset.card_union_of_disjoint hdis, hTc, hUc]
  have himage : (Y ∪ Z).image (entry b) = (T ∪ U).image Subtype.val := by
    rw [Finset.image_union, hY, hZ, Finset.image_union]
  have hphys := finite_population_sum b (Y ∪ Z) (T ∪ U) himage
  have hdiff : stock \ (T ∪ U) = (stock \ T) \ U := by
    ext x
    simp [and_assoc, and_comm, and_left_comm]
  have hpos' : 0 < (stock \ (T ∪ U)).card := by rw [hdiff, ← hremain]; exact hpos
  have hupdate := central_entries_actual_mean_update stock (T ∪ U) centralPoolValue hsub hpos'
  rw [hdiff, ← hremain, hcard, ← hphys] at hupdate
  have hden : (0 : ℝ) < (actualUnusedPool b (reserved ∪ (Y ∪ Z))).card := by exact_mod_cast hpos
  constructor
  · rw [hupdate]
    have heq : centralEntriesMean stock centralPoolValue -
        ((∑ z ∈ Y ∪ Z, (entry b z : ℝ)) - ((Y.card + Z.card : ℕ) : ℝ) *
          centralEntriesMean stock centralPoolValue) /
            ((actualUnusedPool b (reserved ∪ (Y ∪ Z))).card : ℝ) -
          centralEntriesMean stock centralPoolValue =
        -(((∑ z ∈ Y ∪ Z, (entry b z : ℝ)) - ((Y.card + Z.card : ℕ) : ℝ) *
          centralEntriesMean stock centralPoolValue) /
            ((actualUnusedPool b (reserved ∪ (Y ∪ Z))).card : ℝ)) := by ring
    rw [heq, abs_neg, abs_div, abs_of_pos hden]
    exact div_le_div_of_nonneg_right hsum hden.le
  · intro z hz
    have hv : entry b z ∈ (T ∪ U).image Subtype.val := by
      rw [← himage]
      exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
    obtain ⟨v, hv, hvval⟩ := Finset.mem_image.mp hv
    have hw : ∀ x ∈ stock, ∀ y ∈ stock, centralPoolValue y - centralPoolValue x ≤ (poolMaximum n : ℝ) := by
      intro x hx y hy
      exact le_of_lt (actual_unused_pool_strict_width a reserved y hy x hx)
    have hbound := prefix_population_member_mean_width stock centralPoolValue (poolMaximum n) hw v (hsub hv)
    simpa [centralEntriesMean, centralPoolValue, hvval] using hbound

end
end Sude
