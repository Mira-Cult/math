import Sude.FWFullReservationLineIncidence
import Sude.CentralExactPool

namespace Sude
noncomputable section

/-- Every capacity rectangle, including every spare, contributes exactly its designated corner. -/
theorem packed_rectangle_diagonal_exact {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) :
    (packedRectangleSupport hs choice ∩ (mainCells n ∪ antiCells n)).card = L := by
  classical
  let corner : Fin L → Cell n := fun i => packedRectangleCorner hs choice (i, 0)
  have hcorner (i : Fin L) : corner i ∈ mainCells n ∪ antiCells n := by
    have hg := RectanglePacking.designated_corner_geometry hs choice i
    cases hi : choice i
    · exact Finset.mem_union_right _ (by simpa [corner, packedRectangleCorner] using (hg.2 hi).1)
    · exact Finset.mem_union_left _ (by simpa [corner, packedRectangleCorner] using (hg.1 hi).1)
  have hside (i : Fin L) (s : Fin 4)
      (hd : packedRectangleCorner hs choice (i,s) ∈ mainCells n ∪ antiCells n) : s = 0 := by
    have h01 := RectanglePacking.firstRow_secondColumn_off_diagonals hs hL choice i
    have h10 := RectanglePacking.secondRow_firstColumn_off_diagonals hs hL choice i
    have h11 := RectanglePacking.secondRow_secondColumn_off_diagonals hs hL choice i
    fin_cases s <;> simp_all [packedRectangleCorner, Finset.mem_union]
  have heq : packedRectangleSupport hs choice ∩ (mainCells n ∪ antiCells n) =
      Finset.univ.image corner := by
    ext z
    constructor
    · intro hz
      obtain ⟨hp, hd⟩ := Finset.mem_inter.mp hz
      obtain ⟨⟨i,s⟩, _, heq⟩ := Finset.mem_image.mp hp
      have hsz : s = 0 := hside i s (heq ▸ hd)
      subst s
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩
    · intro hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      apply Finset.mem_inter.mpr
      exact ⟨Finset.mem_image.mpr ⟨(i,0), Finset.mem_univ _, rfl⟩, hcorner i⟩
  have hinj : Function.Injective corner := by
    intro i j he
    have hh := packedRectangleCorner_injective hs choice he
    exact congrArg Prod.fst hh
  rw [heq, Finset.card_image_of_injective _ hinj]
  simp

/-- Full FW keepout intersects the two diagonals exactly J times. -/
theorem fw_full_keepout_diagonal_exact {n : ℕ}
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice)
      (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc)) :
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    (full ∩ (mainCells n ∪ antiCells n)).card = fwJointRectangleCount n 254 := by
  classical
  dsimp only
  have hrect : 3 ≤ fwJointRectangleCount n 254 := by simp [fwJointRectangleCount]; omega
  have heq : (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))) ∩
        (mainCells n ∪ antiCells n) = packedRectangleSupport hs choice ∩ (mainCells n ∪ antiCells n) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_inter]
    have hr : z ∈ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) →
      z ∉ mainCells n ∧ z ∉ antiCells n := fun hz => hrows.support_off_diagonals z hz
    have hc : z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc)) →
      z ∉ mainCells n ∧ z ∉ antiCells n := fun hz => (hcols.transposed_support_safe z hz).2
    tauto
  rw [heq]
  exact packed_rectangle_diagonal_exact hs hrect choice
/-- Odd-order union partition: exact unreserved diagonal count after any full keepout. -/
theorem unreserved_diagonal_card_of_overlap {n J : ℕ} (hn : 0 < n) (hodd : Odd n)
    (reserved : Finset (Cell n))
    (hinter : (reserved ∩ (mainCells n ∪ antiCells n)).card = J) :
    (unreservedDiagonalCells reserved).card + J + 1 = 2*n := by
  classical
  have hunion := Finset.card_union_add_card_inter (mainCells n) (antiCells n)
  rw [main_anti_intersection hn hodd, mainCells_card, antiCells_card] at hunion
  simp only [Finset.card_singleton] at hunion
  have hsplit := Finset.card_sdiff_add_card_inter (mainCells n ∪ antiCells n) reserved
  rw [Finset.inter_comm, hinter] at hsplit
  change (unreservedDiagonalCells reserved).card + J = _ at hsplit
  omega
end
end Sude
