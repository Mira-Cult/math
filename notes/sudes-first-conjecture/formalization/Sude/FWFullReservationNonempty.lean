import Sude.FWRoleCellOccupancy
import Sude.ActualUnusedPool

/-! Positive actual unused stock for the supplied full FW geometry. This
proves no numerical mean, seed availability or target existence. -/
namespace Sude
noncomputable section

/-- The exact FW full-reservation formula is strictly smaller than `n²`
through the stated stage budget. No upper bound on `n` is required. -/
theorem fw_full_reservation_card_formula_lt {n P : ℕ}
    (hn : 19485 ≤ n) (hP : P ≤ 238) :
    12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) + 96 * (238 - P) < n * n := by
  have hdiv : 450 * (n / 450) ≤ n := by omega
  have hS : 450 * (5 + 16 + 3 * (n / 450) + P) ≤ 450 * 259 + 3 * n := by nlinarith
  have hm := Nat.mul_le_mul_right (n + 8) hS
  have hsp : 96 * (238 - P) ≤ 96 * 238 := Nat.mul_le_mul_left 96 (Nat.sub_le _ _)
  have hsquare : 19485 * n ≤ n * n := Nat.mul_le_mul_right n hn
  nlinarith

/-- The normalized full FW reservation is strictly smaller than the square,
so its actual unused prescribed pool is nonempty for every supplied square. -/
theorem fw_full_reservation_actual_unused_positive {n P : ℕ}
    (hn : 19485 ≤ n) (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice)
      (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (a : Cell n ≃ Fin (n * n)) :
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    full.card < n * n ∧ 0 < (actualUnusedPool a full).card := by
  dsimp only
  have hocc := fw_role_cell_occupancy hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  dsimp only at hocc
  have hsmall : (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))).card < n * n := by
    rw [hocc.2.2.2.2.2.2.1]
    exact fw_full_reservation_card_formula_lt hn hP
  have hcount := actualUnusedPool_card n a
    (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc)))
  exact ⟨hsmall, by omega⟩

end
end Sude
