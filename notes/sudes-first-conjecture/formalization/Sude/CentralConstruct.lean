import Sude.BalancedReservation
import Sude.CentralStockDepletion

/-! Explicit composition of central diagonals, bounded stock and completion. -/
namespace Sude
noncomputable section

/-- The exact numerical/analytic inputs needed after diagonal preassignment.
These are hypotheses to discharge for a controller, not external imports. -/
structure PostDiagonalAnalyticInputs {n : ℕ} (b : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (bits : ℕ) (ε : ℝ) (D : ℕ) : Prop where
  left : 1 ≤ centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
    ε * poolMaximum n
  right : centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue +
    ε * poolMaximum n ≤ poolMaximum n
  deletions :
    (apInterval
      (centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue - ε * poolMaximum n)
      (centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue + ε * poolMaximum n)
      2 1 ∩ (reserved ∪ unreservedDiagonalCells reserved).image (entry b)).card ≤ D
  gate : (((9 * bits + 6) * n : ℕ) : ℝ) ≤
    (2 * (ε * poolMaximum n) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n)) /
      Real.log (poolMaximum n) - D

/-- Reserving the previously free diagonal cells covers both entire labelled
main diagonals, including a shared center. -/
theorem postDiagonal_contains_both {n : ℕ} (reserved : Finset (Cell n)) :
    mainCells n ⊆ reserved ∪ unreservedDiagonalCells reserved ∧
      antiCells n ⊆ reserved ∪ unreservedDiagonalCells reserved := by
  constructor <;> intro z hz <;> by_cases hr : z ∈ reserved
  · exact Finset.mem_union_left _ hr
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hz, hr⟩)
  · exact Finset.mem_union_left _ hr
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hz, hr⟩)

/-- The bounded central construction, with all internal physical steps
composed. Its remaining inputs are the pair/stock, occupancy, charged
numerical gates and published BMOR/RS hypotheses; it asserts no prime targets. -/
theorem bounded_central_construction_from_pairs (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {n r₀ bits : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (pair : I × Bool → Cell n) (budget : I → ℝ) (η ε : ℝ) (D : ℕ)
    (hη : 0 < η) (hε : 0 ≤ ε) (hn : 20 ≤ n) (hnmax : n ≤ 2 ^ 18) (hodd : Odd n)
    (hinj : Function.Injective pair)
    (hcover : (Finset.univ : Finset (I × Bool)).image pair = reserved)
    (hcenter : centralCell n (by omega) ∉ reserved)
    (hreserved : 4 * reserved.card ≤ n * n)
    (hpair : ∀ i, |(entry a (pair (i, true)) : ℝ) + (entry a (pair (i, false)) : ℝ) -
      2 * ((Lucas.poolTotal n : ℝ) / (n * n : ℕ))| ≤ budget i)
    (hbudget : (∑ i, budget i) / (n * n - reserved.card : ℕ) ≤ η / 4)
    (hlow : 1 + (centralFreeMain (by omega) reserved).card + (centralFreeAnti (by omega) reserved).card ≤
      ((actualUnusedPool a reserved).filter (fun v =>
        (Lucas.poolTotal n : ℝ) / (n * n : ℕ) - η < centralPoolValue v ∧
        centralPoolValue v ≤ (Lucas.poolTotal n : ℝ) / (n * n : ℕ) - η / 2)).card)
    (hhigh : 1 + (centralFreeMain (by omega) reserved).card + (centralFreeAnti (by omega) reserved).card ≤
      ((actualUnusedPool a reserved).filter (fun v =>
        (Lucas.poolTotal n : ℝ) / (n * n : ℕ) + η / 2 < centralPoolValue v ∧
        centralPoolValue v ≤ (Lucas.poolTotal n : ℝ) / (n * n : ℕ) + η)).card)
    (hload : 4 * (r₀ + 6 * bits + 4) ≤ n)
    (hrowlo : ∀ i, r₀ ≤ (LayerPacking.rowUsed (reserved ∪ unreservedDiagonalCells reserved) i).card)
    (hrowhi : ∀ i, (LayerPacking.rowUsed (reserved ∪ unreservedDiagonalCells reserved) i).card ≤ r₀ + (6 * bits + 4))
    (hcollo : ∀ i, r₀ ≤ (LayerPacking.colUsed (reserved ∪ unreservedDiagonalCells reserved) i).card)
    (hcolhi : ∀ i, (LayerPacking.colUsed (reserved ∪ unreservedDiagonalCells reserved) i).card ≤ r₀ + (6 * bits + 4))
    (hpost : ∀ b : Cell n ≃ Fin (n * n),
      (∀ z ∈ reserved, entry b z = entry a z) →
      (∀ z ∈ unreservedDiagonalCells reserved,
        |(entry b z : ℝ) - (Lucas.poolTotal n : ℝ) / (n * n : ℕ)| ≤ η) →
      n * n / 2 ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card →
      |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
          3 * η / (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card →
      PostDiagonalAnalyticInputs b reserved bits ε D) :
    ∃ b c : Cell n ≃ Fin (n * n),
      (∀ z ∈ reserved, entry c z = entry a z) ∧
      (∀ i, |(rowSum c i : ℝ) -
        ((∑ z ∈ rowCells i ∩ reserved, (entry a z : ℝ)) +
          ((rowCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
            (1 + 2 * (9 * bits + 6 : ℕ) * ε) * poolMaximum n + (5 / 2 : ℝ) * η +
              (n : ℝ) * (3 * η / (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card)) ∧
      (∀ i, |(columnSum c i : ℝ) -
        ((∑ z ∈ columnCells i ∩ reserved, (entry a z : ℝ)) +
          ((columnCells i \ reserved).card : ℝ) * centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| <
            (1 + 2 * (9 * bits + 6 : ℕ) * ε) * poolMaximum n + (5 / 2 : ℝ) * η +
              (n : ℝ) * (3 * η / (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card)) ∧
      |(mainSum c : ℝ) - ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) +
        ((1 + (centralFreeMain (by omega) reserved).card : ℕ) : ℝ) *
          centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤ 2 * η ∧
      |(antiSum c : ℝ) - ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) +
        ((1 + (centralFreeAnti (by omega) reserved).card : ℕ) : ℝ) *
          centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤ (201 / 100) * η ∧
      Set.range (entry c) = pool n ∧ Function.Injective (entry c) := by
  have hsmall : reserved.card < n * n := by nlinarith
  have hmean0 := (actual_unused_mean_from_reserved_pairs_source a reserved pair budget hinj hcover hsmall hpair).trans hbudget
  obtain ⟨b, hfixed, hcentral, hcount, hshift, _, hmain, hanti, _, _⟩ :=
    central_diagonals_from_reserved_pairs a reserved pair budget η hη hn hodd hinj hcover hcenter hreserved
      hpair hbudget hlow hhigh
  have hp := hpost b hfixed hcentral hcount hshift
  have hdiags := postDiagonal_contains_both reserved
  obtain ⟨c, hfixedc, hrows, hcols, hmainc, hantic, hpool, hinject⟩ :=
    bmor_balanced_charged_completion bmor upper b (reserved ∪ unreservedDiagonalCells reserved)
      hdiags.1 hdiags.2 hload hrowlo hrowhi hcollo hcolhi ε D hε (by omega) hnmax
      hp.left hp.right hp.deletions hp.gate
  have htransfer := central_diagonal_rows_columns_transfer a b c reserved η
    ((1 + 2 * (9 * bits + 6 : ℕ) * ε) * poolMaximum n) hη.le hfixed hcentral hmean0 hshift hrows hcols
  refine ⟨b, c, ?_, htransfer.1, htransfer.2, ?_, ?_, hpool, hinject⟩
  · intro z hz
    exact (hfixedc z (Finset.mem_union_left _ hz)).trans (hfixed z hz)
  · simpa [hmainc] using hmain
  · simpa [hantic] using hanti

end
end Sude
