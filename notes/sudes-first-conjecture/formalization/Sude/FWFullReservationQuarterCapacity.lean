import Sude.FWFullReservationNonempty

/-! The supplied first-band FW full geometric reservation occupies at most a
quarter of the square. No stock, completion, prime, or flow conclusion. -/
namespace Sude
noncomputable section

/-- The exact full-reservation cardinal formula satisfies the quarter-capacity
bound throughout the first band; no upper bound on the order is needed. -/
theorem fw_full_reservation_formula_quarter {n P : ℕ}
    (hn : 19485 ≤ n) (hP : P ≤ 238) :
    4 * (12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) + 96 * (238 - P)) ≤ n*n := by
  have hdiv : 450 * (n / 450) ≤ n := by omega
  have hS : 450 * (5 + 16 + 3 * (n / 450) + P) ≤ 450 * 259 + 3 * n := by nlinarith
  have hm := Nat.mul_le_mul_right (n + 8) hS
  have hsp : 96 * (238 - P) ≤ 96 * 238 := Nat.mul_le_mul_left 96 (Nat.sub_le _ _)
  have hsquare : 19485 * n ≤ n * n := Nat.mul_le_mul_right n hn
  nlinarith

/-- The actual packed full FW reservation satisfies the same quarter bound.
The exact joint row and transposed-column packing are supplied hypotheses. -/
theorem fw_full_reservation_quarter_capacity {n P : ℕ}
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
      (((bc ++ sc) ++ wc) ++ gc)) :
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    4 * full.card ≤ n * n := by
  dsimp only
  have hocc := fw_role_cell_occupancy hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  dsimp only at hocc
  rw [hocc.2.2.2.2.2.2.1]
  exact fw_full_reservation_formula_quarter hn hP

end
end Sude
