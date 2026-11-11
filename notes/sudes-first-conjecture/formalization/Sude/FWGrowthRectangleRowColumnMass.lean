import Sude.FWGrowthDiagonalPhysical
import Sude.RectanglePairInvoice

/-! Global row and column incidence of the growth rectangle pairs. -/
namespace Sude
noncomputable section

/-- Across every growth stage together, the designated rectangle pairs use
at most the full packed-rectangle line weight. -/
theorem fw_growth_rectangle_weight_le_full {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P * (4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*3) (hc : cols.length = P*3)
    (line : Cell n → Prop) [DecidablePred line] :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    (∑ x : (Fin P × Fin (4*6)) × Fin 2,
      physicalPairLineWeight cells line
        (x.1.1, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (x.1.2,x.2))) ≤
      ∑ p : Fin L × Fin 2, rectanglePairWeight hs choice line p := by
  classical
  dsimp only
  let f : (Fin P × Fin (4*6)) × Fin 2 → Fin L × Fin 2 :=
    fun x => (btGrowingOffsetRectangle offset hoff (finProdFinEquiv x.1), x.2)
  have hf : Function.Injective f := by
    rintro ⟨⟨j,r⟩,p⟩ ⟨⟨j',r'⟩,p'⟩ h
    have hp : p = p' := congrArg Prod.snd h
    have hrect := congrArg Prod.fst h
    have hpair : (j,r) = (j',r') := finProdFinEquiv.injective
      (btGrowingOffsetRectangle_injective offset hoff hrect)
    exact Prod.ext hpair hp
  have hweight (x : (Fin P × Fin (4*6)) × Fin 2) :
      physicalPairLineWeight
        (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice rows cols hr hc) line
        (x.1.1, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (x.1.2,x.2)) =
      rectanglePairWeight hs choice line (f x) := by
    unfold physicalPairLineWeight rectanglePairWeight
    rw [fw_growth_offset_rectangle_cell offset hoff hs choice rows cols hr hc x.1.1 x.1.2 x.2 false,
      fw_growth_offset_rectangle_cell offset hoff hs choice rows cols hr hc x.1.1 x.1.2 x.2 true]
  calc
    _ = ∑ x : (Fin P × Fin (4*6)) × Fin 2, rectanglePairWeight hs choice line (f x) := by
      exact Finset.sum_congr rfl (fun x _ => hweight x)
    _ = ∑ p ∈ Finset.univ.image f, rectanglePairWeight hs choice line p := by
      symm
      exact Finset.sum_image hf.injOn
    _ ≤ ∑ p : Fin L × Fin 2, rectanglePairWeight hs choice line p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro p _ _
      unfold rectanglePairWeight
      split_ifs <;> norm_num

/-- All growth rectangle pairs together meet a fixed row in at most two
endpoint incidences. -/
theorem fw_growth_rectangle_row_mass {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P * (4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*3) (hc : cols.length = P*3) (r : Fin n) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    (∑ x : (Fin P × Fin (4*6)) × Fin 2,
      physicalPairLineWeight cells (fun c => c.1 = r)
        (x.1.1, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (x.1.2,x.2))) ≤ 2 := by
  have h := fw_growth_rectangle_weight_le_full offset hoff hs choice rows cols hr hc (fun c => c.1 = r)
  apply h.trans
  rw [rectanglePairWeight_sum_eq_card]
  exact_mod_cast packedRectangle_row_card_le_two hs choice r

/-- All growth rectangle pairs together meet a fixed column in at most two
endpoint incidences. -/
theorem fw_growth_rectangle_column_mass {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P * (4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*3) (hc : cols.length = P*3) (c : Fin n) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    (∑ x : (Fin P × Fin (4*6)) × Fin 2,
      physicalPairLineWeight cells (fun z => z.2 = c)
        (x.1.1, prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (x.1.2,x.2))) ≤ 2 := by
  have h := fw_growth_rectangle_weight_le_full offset hoff hs choice rows cols hr hc (fun z => z.2 = c)
  apply h.trans
  rw [rectanglePairWeight_sum_eq_card]
  exact_mod_cast packedRectangle_column_card_le_two hs choice c

end
end Sude
