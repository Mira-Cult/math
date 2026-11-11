import Sude.FWSeedOffsetActualRowColumn

/-! Exact unsquared line incidences for the actual offset seed slots.
The rectangle contribution remains explicit; no allocation or complete-line
bound is asserted. -/
namespace Sude
noncomputable section

theorem layer_row_weight_sum {n : ℕ} (π f : Equiv.Perm (Fin n)) (r : Fin n) :
    (∑ i, LayerPacking.layerRowWeight π f r i) = 2 := by
  simp [LayerPacking.layerRowWeight_eq, Finset.sum_add_distrib]
  norm_num

theorem layer_column_weight_sum {n : ℕ} (π f : Equiv.Perm (Fin n)) (c : Fin n) :
    (∑ i, LayerPacking.layerColumnWeight π f c i) = 2 := by
  simp [LayerPacking.layerColumnWeight_eq]

/-- The unsquared contribution of the 24 seed rectangles in one stage. -/
def fwSeedRectangleStageLineWeight {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (line : Cell n → Prop) [DecidablePred line] (j : Fin 16) : ℝ :=
  ∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
    rectanglePairWeight hs choice line (fwSeedRectangle hseed (finProdFinEquiv (j, rect)), pair)

/-- Each of the three row and three transposed-column layers contributes two
ordinary incidences, independently of whether an edge is a loop. -/
theorem fw_seed_existing_row_line_weight {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (j : Fin 16) (r : Fin n) :
    (∑ q : Fin (6 * (n + 8)),
      physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun c => c.1 = r) (j, q)) =
      fwSeedRectangleStageLineWeight hseed hs choice (fun c => c.1 = r) j + 12 := by
  classical
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  let w := fun q : Fin (6 * (n + 8)) => physicalPairLineWeight
    (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) (fun c => c.1 = r) (j, q)
  calc
    ∑ q, w q = ∑ tag : PrefixStagePair 6 3 n, w (e tag) :=
      (e.sum_comp w).symm
    _ = _ := by
      simp only [w, e, Equiv.ofBijective_apply,
        fw_seed_existing_row_weight_at_label hseed hs choice sr sc hsr hsc j r]
      simp [fwSeedOffsetRowIncidence, fwSeedRectangleStageLineWeight,
        Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
        layer_row_weight_sum, layer_column_weight_sum]
      norm_num

theorem fw_seed_existing_column_line_weight {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (j : Fin 16) (c : Fin n) :
    (∑ q : Fin (6 * (n + 8)),
      physicalPairLineWeight (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc)
        (fun x => x.2 = c) (j, q)) =
      fwSeedRectangleStageLineWeight hseed hs choice (fun x => x.2 = c) j + 12 := by
  classical
  let hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
  let hdiag : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
  let hexact : (4 * 6) * 2 + 2 * (3 * n) = 6 * (n + 8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  let w := fun q : Fin (6 * (n + 8)) => physicalPairLineWeight
    (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) (fun x => x.2 = c) (j, q)
  calc
    ∑ q, w q = ∑ tag : PrefixStagePair 6 3 n, w (e tag) :=
      (e.sum_comp w).symm
    _ = _ := by
      simp only [w, e, Equiv.ofBijective_apply,
        fw_seed_existing_column_weight_at_label hseed hs choice sr sc hsr hsc j c]
      simp [fwSeedOffsetColumnIncidence, fwSeedRectangleStageLineWeight,
        Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
        layer_row_weight_sum, layer_column_weight_sum]
      norm_num

end
end Sude
