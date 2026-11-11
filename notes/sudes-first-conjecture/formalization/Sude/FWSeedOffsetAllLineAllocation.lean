import Sude.FWSeedOffsetActualRowColumn
import Sude.PhysicalAllLineWeights
import Sude.StageSquaredInvoice

/-! Simultaneous concentration on the actual offset seed pair slots. -/
namespace Sude
noncomputable section

/-- Actual pair incidence for each labelled physical line at the FW offset seed cells. -/
noncomputable def fwSeedOffsetAllLineWeight {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (l : Fin ((n + n) + 2)) (j : Fin 16) (q : Fin (6 * (n + 8))) : ℝ :=
  physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
    (fun c => c ∈ physicalAllLineCells l) (j, q)

/-- Conditional concentration for all labelled lines using the actual offset seed pair weights.
No physical reallocation, completion, prime target, or mean-line bound is concluded. -/
theorem fw_seed_offset_all_line_allocation {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3)
    (hsc : sc.length = 16 * 3) (reservedRows reservedCols : Finset (Cell n))
    (packedRows : LayerPacking.PackedLayers reservedRows sr)
    (packedCols : LayerPacking.PackedLayers reservedCols sc)
    (values : Fin 16 → Fin (6 * (n + 8)) → ℝ) (lo upper : Fin 16 → ℝ)
    (z V : ℝ) (hvalues : ∀ j a, values j a ∈ Set.Icc (lo j) (upper j))
    (hwidth : ∀ j, (upper j - lo j) ^ 2 ≤ z ^ 2)
    (hbudget : 18 * (∑ j, (upper j - lo j) ^ 2) + 4 * z ^ 2 ≤ V) :
    ∃ ω : Fin 16 → Equiv.Perm (Fin (6 * (n + 8))), ∀ l,
      |stageLineCentered (fun _ _ => Finset.univ)
        (fwSeedOffsetAllLineWeight hseed hs
          (fwBridgeSeedRectangleChoice hrect hseed otherChoice) sr sc hsr hsc) values l ω| ≤
      Real.sqrt (V * Real.log (4 * (((n + n) + 2 : ℕ) : ℝ)) / 2) := by
  classical
  let choice := fwBridgeSeedRectangleChoice hrect hseed otherChoice
  let slots : Fin ((n + n) + 2) → Fin 16 → Finset (Fin (6 * (n + 8))) := fun _ _ => Finset.univ
  let weights := fwSeedOffsetAllLineWeight hseed hs choice sr sc hsr hsc
  let width : Fin 16 → ℝ := fun j => upper j - lo j
  have hsum : 0 ≤ ∑ j, (width j) ^ 2 := Finset.sum_nonneg (by intro j _; exact sq_nonneg _)
  have hV : 0 ≤ V := by nlinarith [sq_nonneg z]
  have hlu : ∀ j, lo j ≤ upper j := by
    intro j
    have hQ : 0 < 6 * (n + 8) := by omega
    exact (hvalues j ⟨0, hQ⟩).1.trans (hvalues j ⟨0, hQ⟩).2
  have hnonneg : ∀ l j q, q ∈ slots l j → 0 ≤ weights l j q := by
    intro l j q _
    simp only [weights, fwSeedOffsetAllLineWeight, physicalPairLineWeight]
    split_ifs <;> norm_num
  have hinvoice : ∀ l, (∑ j, (upper j - lo j) ^ 2 *
      ∑ q ∈ slots l j, (weights l j q) ^ 2) ≤ V := by
    intro l
    cases hl : (finSumFinEquiv (m := n + n) (n := 2)).symm l with
    | inl rc =>
      cases hrc : (finSumFinEquiv (m := n) (n := n)).symm rc with
      | inl r =>
        have h := fw_seed_existing_row_weighted_invoice hseed hs choice sr sc hsr hsc reservedRows
          packedRows r width z hwidth
        have hh : (∑ j, (upper j - lo j) ^ 2 * ∑ q ∈ slots l j, (weights l j q) ^ 2) ≤
            18 * (∑ j, (width j) ^ 2) + 4 * z ^ 2 := by
          simpa [slots, weights, fwSeedOffsetAllLineWeight, physicalAllLineCells, hl, hrc, width] using h
        exact hh.trans hbudget
      | inr c =>
        have h := fw_seed_existing_column_weighted_invoice hseed hs choice sr sc hsr hsc reservedCols
          packedCols c width z hwidth
        have hh : (∑ j, (upper j - lo j) ^ 2 * ∑ q ∈ slots l j, (weights l j q) ^ 2) ≤
            18 * (∑ j, (width j) ^ 2) + 4 * z ^ 2 := by
          simpa [slots, weights, fwSeedOffsetAllLineWeight, physicalAllLineCells, hl, hrc, width] using h
        exact hh.trans hbudget
    | inr diag =>
      by_cases hzero : diag = 0
      · have h := fw_seed_existing_main_weighted_invoice hrect hseed hs hL otherChoice sr sc hsr hsc
          reservedRows reservedCols packedRows packedCols width
        have he : (∑ j, (upper j - lo j) ^ 2 * ∑ q ∈ slots l j, (weights l j q) ^ 2) =
            12 * ∑ j, (width j) ^ 2 := by
          simpa [slots, weights, fwSeedOffsetAllLineWeight, physicalAllLineCells, hl, hzero, choice, width] using h
        rw [he]
        nlinarith [sq_nonneg z]
      · have h := fw_seed_existing_anti_weighted_invoice hrect hseed hs hL otherChoice sr sc hsr hsc
          reservedRows reservedCols packedRows packedCols width
        have he : (∑ j, (upper j - lo j) ^ 2 * ∑ q ∈ slots l j, (weights l j q) ^ 2) =
            12 * ∑ j, (width j) ^ 2 := by
          simpa [slots, weights, fwSeedOffsetAllLineWeight, physicalAllLineCells, hl, hzero, choice, width] using h
        rw [he]
        nlinarith [sq_nonneg z]
  simpa [slots, weights, choice] using
    stageLines_exists_of_squared_invoice (by omega : 0 < (n+n)+2) slots weights values lo upper V
      hV hlu hnonneg hvalues hinvoice

end
end Sude
