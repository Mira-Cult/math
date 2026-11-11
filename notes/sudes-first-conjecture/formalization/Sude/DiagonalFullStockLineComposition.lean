import Sude.DiagonalFullStockCenterBatches
import Sude.DiagonalFullStockLineShift

/-! Combine the center and two batch expectation invoices on one witness. -/
namespace Sude
noncomputable section

/-- After handling an unreserved center, choose and install both full-stock
batches. Every supplied line meeting the two batches in at most two cells has
its conditional completion expectation shifted by at most `5X/2 + kX/N`.
The same placement is used for every line. This is not a completed line sum. -/
theorem actual_center_batches_line_expectation {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (reserved Y Z : Finset (Cell n)) (center : Cell n)
    (hcenter : center ∉ reserved) (hYR : Disjoint Y reserved) (hZR : Disjoint Z reserved)
    (hYZ : Disjoint Y Z) (hYc : center ∉ Y) (hZc : center ∉ Z)
    (hroom : 1 + Y.card + Z.card < (actualUnusedPool a reserved).card) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      0 < (actualUnusedPool b ((reserved ∪ {center}) ∪ (Y ∪ Z))).card ∧
      ∀ line : Finset (Cell n), (line ∩ (Y ∪ Z)).card ≤ 2 →
        |((∑ z ∈ line ∩ ((reserved ∪ {center}) ∪ (Y ∪ Z)), (entry b z : ℝ)) +
            ((line \ ((reserved ∪ {center}) ∪ (Y ∪ Z))).card : ℝ) *
              centralEntriesMean (actualUnusedPool b ((reserved ∪ {center}) ∪ (Y ∪ Z))) centralPoolValue) -
          ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
            ((line \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (5 / 2 : ℝ) * poolMaximum n +
            ((line \ ((reserved ∪ {center}) ∪ (Y ∪ Z))).card : ℝ) *
              ((poolMaximum n : ℝ) /
                (actualUnusedPool b ((reserved ∪ {center}) ∪ (Y ∪ Z))).card) := by
  classical
  obtain ⟨b₀, b, T, U, hfixed₀, hexpect, hT, hU, hTc, hUc, hY, hZ,
    hfixed, hremain, hpos, _, _, hsum⟩ :=
    actual_center_and_two_full_stock_batches a reserved Y Z center hcenter hYR hZR hYZ hYc hZc hroom
  have hdisY : Disjoint (reserved ∪ {center}) Y :=
    (Finset.disjoint_union_right.mpr ⟨hYR, by simpa using hYc⟩).symm
  have hdisZ : Disjoint (reserved ∪ {center}) Z :=
    (Finset.disjoint_union_right.mpr ⟨hZR, by simpa using hZc⟩).symm
  have hdis : Disjoint (reserved ∪ {center}) (Y ∪ Z) :=
    Finset.disjoint_union_right.mpr ⟨hdisY, hdisZ⟩
  refine ⟨b, ?_, hpos, ?_⟩
  · intro z hz
    exact (hfixed z (Finset.mem_union_left _ hz)).trans (hfixed₀ z hz)
  · intro line hline
    have hbatch := placed_full_stock_line_expectation_shift b₀ b (reserved ∪ {center}) Y Z line
      T U hT hU hTc hUc hY hZ hdis hfixed hremain hpos hsum hline
    have hcenter' := hexpect line
    have htriangle := abs_sub_le
      ((∑ z ∈ line ∩ ((reserved ∪ {center}) ∪ (Y ∪ Z)), (entry b z : ℝ)) +
        ((line \ ((reserved ∪ {center}) ∪ (Y ∪ Z))).card : ℝ) *
          centralEntriesMean (actualUnusedPool b ((reserved ∪ {center}) ∪ (Y ∪ Z))) centralPoolValue)
      ((∑ z ∈ line ∩ (reserved ∪ {center}), (entry b₀ z : ℝ)) +
        ((line \ (reserved ∪ {center})).card : ℝ) *
          centralEntriesMean (actualUnusedPool b₀ (reserved ∪ {center})) centralPoolValue)
      ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
        ((line \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)
    linarith

end
end Sude
