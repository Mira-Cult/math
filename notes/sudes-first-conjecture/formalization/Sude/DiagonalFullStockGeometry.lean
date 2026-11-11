import Sude.DiagonalFullStockLineComposition
import Sude.CentralPairDiagonal

/-! DQ2 for the actual free diagonal cells. -/
namespace Sude
noncomputable section

/-- The DQ center and full-stock placement specialized to the actual free
diagonal cells of an odd square, with the full reservation charged. -/
theorem odd_diagonal_full_stock_expectation {n : ℕ} (a : Cell n ≃ Fin (n*n))
    (reserved : Finset (Cell n)) (hn : 7 ≤ n) (hodd : Odd n)
    (hcenter : centralCell n (by omega) ∉ reserved) (hreserve : 4 * reserved.card ≤ n*n) :
    ∃ b : Cell n ≃ Fin (n*n),
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      2*n ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card ∧
      ∀ line : Finset (Cell n), (line ∩ unreservedDiagonalCells reserved).card ≤ 2 →
        |((∑ z ∈ line ∩ (reserved ∪ unreservedDiagonalCells reserved), (entry b z : ℝ)) +
            ((line \ (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) *
              centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue) -
          ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
            ((line \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          (5 / 2 : ℝ) * poolMaximum n +
            ((line \ (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) *
              ((poolMaximum n : ℝ) /
                (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card) := by
  classical
  let hp : 0 < n := by omega
  let center := centralCell n hp
  let Y := centralFreeMain hp reserved
  let Z := centralFreeAnti hp reserved
  obtain ⟨_, hYcard, hZcard, _, hYR, hZR, hXY, hXZ, hYZ, _, _⟩ :=
    central_free_diagonal_geometry hp hodd reserved hcenter
  change Y.card ≤ n - 1 at hYcard
  change Z.card ≤ n - 1 at hZcard
  have hYc : center ∉ Y := by simpa [center, Y] using hXY
  have hZc : center ∉ Z := by simpa [center, Z] using hXZ
  have hc := actualUnusedPool_card n a reserved
  have hn2 : 7*n ≤ n*n := by nlinarith
  have hs : 1+Y.card+Z.card+1 ≤ 2*n := by omega
  have hroom : 1+Y.card+Z.card < (actualUnusedPool a reserved).card := by nlinarith
  obtain ⟨b, hfixed, _, hline⟩ := actual_center_batches_line_expectation a reserved Y Z center
    hcenter hYR hZR hYZ hYc hZc hroom
  have hpart : ({center} : Finset (Cell n)) ∪ Y ∪ Z = unreservedDiagonalCells reserved :=
    unreservedDiagonalCells_partition hp hodd reserved hcenter
  have hfinal : (reserved ∪ {center}) ∪ (Y ∪ Z) = reserved ∪ unreservedDiagonalCells reserved := by
    rw [← hpart]
    ext x
    simp only [Finset.mem_union]
    tauto
  have hdis : Disjoint reserved (unreservedDiagonalCells reserved) := by
    apply Finset.disjoint_left.mpr
    intro z hz hdiag
    exact (Finset.mem_sdiff.mp hdiag).2 hz
  have hdisYZ : Disjoint Y Z := hYZ
  have hdisCY : Disjoint ({center} : Finset (Cell n)) Y := by simpa [center, Y] using hXY
  have hdisCZ : Disjoint ({center} : Finset (Cell n)) Z := by simpa [center, Z] using hXZ
  have hcarddiag : (unreservedDiagonalCells reserved).card = 1+Y.card+Z.card := by
    rw [← hpart, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisCZ, hdisYZ⟩),
      Finset.card_union_of_disjoint hdisCY]
    simp
  have hcardres : (reserved ∪ unreservedDiagonalCells reserved).card = reserved.card + (1+Y.card+Z.card) := by
    rw [Finset.card_union_of_disjoint hdis, hcarddiag]
  have hbcard := actualUnusedPool_card n b (reserved ∪ unreservedDiagonalCells reserved)
  have hfinalcount : 2*n ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card := by
    rw [hcardres] at hbcard
    nlinarith
  refine ⟨b, hfixed, hfinalcount, ?_⟩
  intro line hlineD
  have hsub : line ∩ (Y ∪ Z) ⊆ line ∩ unreservedDiagonalCells reserved := by
    intro z hz
    obtain ⟨hzline, hzYZ⟩ := Finset.mem_inter.mp hz
    refine Finset.mem_inter.mpr ⟨hzline, ?_⟩
    rw [← hpart]
    simp only [Finset.mem_union] at *
    tauto
  have hi := (Finset.card_le_card hsub).trans hlineD
  have result := hline line hi
  rw [hfinal] at result
  exact result

/-- Under the same reservation budget, every line with at most n cells and
at most two free diagonal cells has conditional expectation change ≤ 3X. -/
theorem odd_diagonal_full_stock_three_x {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (hn : 7 ≤ n) (hodd : Odd n)
    (hcenter : centralCell n (by omega) ∉ reserved) (hreserve : 4 * reserved.card ≤ n * n) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      2 * n ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card ∧
      ∀ line : Finset (Cell n), line.card ≤ n →
        (line ∩ unreservedDiagonalCells reserved).card ≤ 2 →
        |((∑ z ∈ line ∩ (reserved ∪ unreservedDiagonalCells reserved), (entry b z : ℝ)) +
            ((line \ (reserved ∪ unreservedDiagonalCells reserved)).card : ℝ) *
              centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue) -
          ((∑ z ∈ line ∩ reserved, (entry a z : ℝ)) +
            ((line \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤
          3 * (poolMaximum n : ℝ) := by
  obtain ⟨b, hfixed, hN, hline⟩ := odd_diagonal_full_stock_expectation a reserved hn hodd hcenter hreserve
  refine ⟨b, hfixed, hN, ?_⟩
  intro line hsize hinc
  have h := hline line hinc
  let N := (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card
  let k := (line \ (reserved ∪ unreservedDiagonalCells reserved)).card
  have hk : k ≤ n := (Finset.card_le_card Finset.sdiff_subset).trans hsize
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkN : (2 : ℝ) * k ≤ N := by exact_mod_cast (show 2 * k ≤ N by omega)
  have hratio : (k : ℝ) / N ≤ 1 / 2 := by
    apply (div_le_iff₀ hNR).2
    linarith
  have hX : 0 ≤ (poolMaximum n : ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_left hratio hX
  have heq : (k : ℝ) * ((poolMaximum n : ℝ) / N) =
      (poolMaximum n : ℝ) * ((k : ℝ) / N) := by ring
  dsimp [k, N] at heq hm
  rw [heq] at h
  nlinarith

end
end Sude
