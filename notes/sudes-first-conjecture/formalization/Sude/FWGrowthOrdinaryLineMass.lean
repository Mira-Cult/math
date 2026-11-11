import Sude.PhysicalAllLineWeights
import Sude.FWGrowthDiagonalPhysical

/-! The exact column mass for actual ordinary growth pair slots. -/
namespace Sude
noncomputable section

/-- The two endpoints count separately, even if they coincide. Rows and columns
contribute four in total; the two labelled diagonals contribute their weights. -/
theorem physical_pair_all_line_weight_sum {α : Type*} {n : ℕ}
    (cells : α × Bool → Cell n) (i : α) :
    (∑ l : Fin ((n+n)+2), physicalPairLineWeight cells
      (fun c => c ∈ physicalAllLineCells l) i) =
      4 + physicalPairLineWeight cells (fun c => c ∈ mainCells n) i +
        physicalPairLineWeight cells (fun c => c ∈ antiCells n) i := by
  classical
  let f : Fin ((n+n)+2) → ℝ := fun l => physicalPairLineWeight cells
    (fun c => c ∈ physicalAllLineCells l) i
  let e : (Fin (n+n) ⊕ Fin 2) ≃ Fin ((n+n)+2) := finSumFinEquiv
  let e2 : (Fin n ⊕ Fin n) ≃ Fin (n+n) := finSumFinEquiv
  have h₁ := e.sum_comp f
  have h₂ := e2.sum_comp (fun k => f (e (Sum.inl k)))
  have hr (r : Fin n) : f (e (Sum.inl (e2 (Sum.inl r)))) =
      physicalPairLineWeight cells (fun c => c ∈ rowCells r) i := by
    simp only [f, physicalAllLineCells, ← show finSumFinEquiv = e from rfl,
      ← show finSumFinEquiv = e2 from rfl, Equiv.symm_apply_apply]
  have hc (c : Fin n) : f (e (Sum.inl (e2 (Sum.inr c)))) =
      physicalPairLineWeight cells (fun z => z ∈ columnCells c) i := by
    simp only [f, physicalAllLineCells, ← show finSumFinEquiv = e from rfl,
      ← show finSumFinEquiv = e2 from rfl, Equiv.symm_apply_apply]
  have hd (k : Fin 2) : f (e (Sum.inr k)) =
      physicalPairLineWeight cells (fun c => c ∈ if k = 0 then mainCells n else antiCells n) i := by
    simp only [f, physicalAllLineCells, ← show finSumFinEquiv = e from rfl,
      Equiv.symm_apply_apply]
  change (∑ l, f l) = _
  rw [← h₁, Fintype.sum_sum_type, ← h₂, Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [hr, hc, hd]
  simp [physicalPairLineWeight, Finset.sum_add_distrib]
  <;> ring

/-- The exact physical slot weight is nonnegative for every labelled line. -/
theorem physical_pair_all_line_weight_nonneg {α : Type*} {n : ℕ}
    (cells : α × Bool → Cell n) (i : α) (l : Fin ((n+n)+2)) :
    0 ≤ physicalPairLineWeight cells (fun c => c ∈ physicalAllLineCells l) i := by
  classical
  unfold physicalPairLineWeight
  positivity


/-- Every actual ordinary growth pair has total labelled-line incidence four.
Packing only excludes diagonals; no balanced rectangle choice is needed. -/
theorem fw_growth_ordinary_all_line_mass {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*3) (hc : cols.length = P*3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows rows)
    (hcols : LayerPacking.PackedLayers reservedCols cols)
    (j : Fin P) (i : Fin (6*(n+8))) (hi : i ∈ fwGrowthOrdinarySlots n) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    (∑ l : Fin ((n+n)+2), physicalPairLineWeight cells
      (fun c => c ∈ physicalAllLineCells l) (j,i)) = 4 := by
  classical
  dsimp only
  obtain ⟨⟨tag,k,edge⟩, _, rfl⟩ := Finset.mem_image.mp hi
  have hf := fw_growth_ordinary_off_diagonals offset hoff hs choice rows cols hr hc
    reservedRows reservedCols hrows hcols j tag k edge false
  have ht := fw_growth_ordinary_off_diagonals offset hoff hs choice rows cols hr hc
    reservedRows reservedCols hrows hcols j tag k edge true
  have hw := physical_pair_all_line_weight_sum
    (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc)
    (j, prefixOrdinaryPairIndex (show (4*6)*2+2*(3*n) ≤ 6*(n+8) by omega) (tag,k,edge))
  simpa [physicalPairLineWeight, hf.1, hf.2, ht.1, ht.2] using hw


/-- The actual unscaled physical weights satisfy the DP1 column bound. -/
theorem fw_growth_ordinary_all_line_mass_le_five {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*3) (hc : cols.length = P*3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows rows)
    (hcols : LayerPacking.PackedLayers reservedCols cols)
    (j : Fin P) (i : Fin (6*(n+8))) (hi : i ∈ fwGrowthOrdinarySlots n) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    (∑ l : Fin ((n+n)+2), physicalPairLineWeight cells
      (fun c => c ∈ physicalAllLineCells l) (j,i)) ≤ 5 := by
  dsimp only
  rw [fw_growth_ordinary_all_line_mass offset hoff hs choice rows cols hr hc
    reservedRows reservedCols hrows hcols j i hi]
  norm_num

/-- Scaling ordinary incidence by 5/4 gives the DP1 column budget exactly. -/
theorem fw_growth_ordinary_scaled_line_mass {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*3) (hc : cols.length = P*3)
    (reservedRows reservedCols : Finset (Cell n))
    (hrows : LayerPacking.PackedLayers reservedRows rows)
    (hcols : LayerPacking.PackedLayers reservedCols cols)
    (j : Fin P) (i : Fin (6*(n+8))) (hi : i ∈ fwGrowthOrdinarySlots n) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    (∑ l : Fin ((n+n)+2), (5/4 : ℝ) * physicalPairLineWeight cells
      (fun c => c ∈ physicalAllLineCells l) (j,i)) = 5 := by
  classical
  dsimp only
  rw [← Finset.mul_sum, fw_growth_ordinary_all_line_mass offset hoff hs choice rows cols hr hc
    reservedRows reservedCols hrows hcols j i hi]
  norm_num


/-- Every scaled physical line weight remains nonnegative. -/
theorem physical_pair_scaled_all_line_weight_nonneg {α : Type*} {n : ℕ}
    (cells : α × Bool → Cell n) (i : α) (l : Fin ((n+n)+2)) :
    0 ≤ (5/4 : ℝ) * physicalPairLineWeight cells
      (fun c => c ∈ physicalAllLineCells l) i := by
  exact mul_nonneg (by norm_num) (physical_pair_all_line_weight_nonneg cells i l)

end
end Sude
