import Sude.DiagonalCenterExposure
import Sude.DiagonalFullStockPlacement

/-! One same-witness composition of full-stock center and two batch placement.
The supplied free sets and later completion remain separate obligations. -/
namespace Sude
noncomputable section

/-- Place an unreserved center, then two disjoint cell families using the
actual post-center unused pool. The first square retains the simultaneous
conditional-expectation bound and the second preserves that chosen center. -/
theorem actual_center_and_two_full_stock_batches {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (reserved Y Z : Finset (Cell n)) (center : Cell n)
    (hcenter : center ∉ reserved) (hYR : Disjoint Y reserved) (hZR : Disjoint Z reserved)
    (hYZ : Disjoint Y Z) (hYc : center ∉ Y) (hZc : center ∉ Z)
    (hroom : 1 + Y.card + Z.card < (actualUnusedPool a reserved).card) :
    ∃ b₀ b : Cell n ≃ Fin (n * n), ∃ T U : Finset (pool n),
      (∀ z ∈ reserved, entry b₀ z = entry a z) ∧
      (∀ line : Finset (Cell n),
        |((∑ z ∈ line ∩ (reserved ∪ {center}), (entry b₀ z : ℝ)) +
            ((line \ (reserved ∪ {center})).card : ℝ) *
              centralEntriesMean (actualUnusedPool b₀ (reserved ∪ {center})) centralPoolValue) -
          ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
            ((line \ reserved).card : ℝ) *
              centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (poolMaximum n : ℝ) / 2) ∧
      T ⊆ actualUnusedPool b₀ (reserved ∪ {center}) ∧
      U ⊆ actualUnusedPool b₀ (reserved ∪ {center}) \ T ∧
      T.card = Y.card ∧ U.card = Z.card ∧
      Y.image (entry b) = T.image Subtype.val ∧ Z.image (entry b) = U.image Subtype.val ∧
      (∀ z ∈ reserved ∪ {center}, entry b z = entry b₀ z) ∧
      actualUnusedPool b ((reserved ∪ {center}) ∪ (Y ∪ Z)) =
        (actualUnusedPool b₀ (reserved ∪ {center}) \ T) \ U ∧
      0 < (actualUnusedPool b ((reserved ∪ {center}) ∪ (Y ∪ Z))).card ∧
      |(∑ z ∈ Y, (entry b z : ℝ)) - (Y.card : ℝ) *
        centralEntriesMean (actualUnusedPool b₀ (reserved ∪ {center})) centralPoolValue| ≤
          (poolMaximum n : ℝ) / 2 ∧
      |(∑ z ∈ Z, (entry b z : ℝ)) - (Z.card : ℝ) *
        centralEntriesMean (actualUnusedPool b₀ (reserved ∪ {center}) \ T) centralPoolValue| ≤
          (poolMaximum n : ℝ) / 2 ∧
      |(∑ z ∈ Y ∪ Z, (entry b z : ℝ)) - ((Y.card + Z.card : ℕ) : ℝ) *
        centralEntriesMean (actualUnusedPool b₀ (reserved ∪ {center})) centralPoolValue| ≤
          (poolMaximum n : ℝ) := by
  classical
  obtain ⟨b₀, hfixed₀, _, hexpect⟩ :=
    actual_center_preserves_line_expectations a reserved center hcenter (by omega)
  have hcard₀ := actualUnusedPool_card n a reserved
  have hcard₁ := actualUnusedPool_card n b₀ (reserved ∪ {center})
  have hreserve : (reserved ∪ {center}).card = reserved.card + 1 := by
    rw [Finset.card_union_of_disjoint]
    · simp
    · simpa using hcenter
  have hroom₁ : Y.card + Z.card < (actualUnusedPool b₀ (reserved ∪ {center})).card := by omega
  have hYR' : Disjoint Y (reserved ∪ {center}) :=
    Finset.disjoint_union_right.mpr ⟨hYR, by simpa using hYc⟩
  have hZR' : Disjoint Z (reserved ∪ {center}) :=
    Finset.disjoint_union_right.mpr ⟨hZR, by simpa using hZc⟩
  obtain ⟨b, T, U, hT, hU, hTc, hUc, hY, hZ, hfixed, hremain, hpos, hfirst, hsecond, hsum⟩ :=
    actual_unused_pool_place_two_batches b₀ (reserved ∪ {center}) Y Z hYR' hZR' hYZ hroom₁
  exact ⟨b₀, b, T, U, hfixed₀, hexpect, hT, hU, hTc, hUc, hY, hZ,
    hfixed, hremain, hpos, hfirst, hsecond, hsum⟩

end
end Sude
