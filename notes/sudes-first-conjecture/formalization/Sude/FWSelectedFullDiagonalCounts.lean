import Sude.ActiveRectangleDiagonalGeometry
import Sude.FWSelectedChoiceFullBalance
import Sude.FWThetaFamilyDQRFInputs

/-! Exact main and anti-diagonal reservation counts for one selected family.
The full reservation includes every spare rectangle; no value or prime
assertion is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The selected full rectangle reservation has the same number of main and
anti corners, and therefore the free portions of both diagonals have the same
size. The physical row and column layers are disjoint from both diagonals. -/
theorem fw_selected_full_diagonal_counts {n : ℕ} (hnlo : 19485 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254)
      (fwSelectedThetaChoice hnlo otherChoice)) :
    let K := 12 * (5 + 16 + 3 * (n / 450) + 238)
    (fwThetaFamilyFull f ∩ mainCells n).card = K ∧
    (fwThetaFamilyFull f ∩ antiCells n).card = K ∧
    (mainCells n \ fwThetaFamilyFull f).card = n - K ∧
    (antiCells n \ fwThetaFamilyFull f).card = n - K := by
  classical
  dsimp only
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let full := fwThetaFamilyFull f
  have hL : 3 ≤ fwJointRectangleCount n 254 := by
    have h := f.hrect
    omega
  have hm : full ∩ mainCells n = packedRectangleSupport f.hs choice ∩ mainCells n := by
    ext z
    simp only [full, fwThetaFamilyFull, Finset.mem_inter, Finset.mem_union]
    have hr : z ∈ LayerPacking.layersSupport (((f.br ++ f.sr) ++ f.wr) ++ f.gr) → z ∉ mainCells n :=
      fun hz => (f.hrows.support_off_diagonals z hz).1
    have hc : z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport (((f.bc ++ f.sc) ++ f.wc) ++ f.gc)) → z ∉ mainCells n :=
      fun hz => ((f.hcols.transposed_support_safe z hz).2).1
    tauto
  have ha : full ∩ antiCells n = packedRectangleSupport f.hs choice ∩ antiCells n := by
    ext z
    simp only [full, fwThetaFamilyFull, Finset.mem_inter, Finset.mem_union]
    have hr : z ∈ LayerPacking.layersSupport (((f.br ++ f.sr) ++ f.wr) ++ f.gr) → z ∉ antiCells n :=
      fun hz => (f.hrows.support_off_diagonals z hz).2
    have hc : z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport (((f.bc ++ f.sc) ++ f.wc) ++ f.gc)) → z ∉ antiCells n :=
      fun hz => ((f.hcols.transposed_support_safe z hz).2).2
    tauto
  have hrect : activeRectangleSupport f.hs choice Finset.univ = packedRectangleSupport f.hs choice := by
    simp [activeRectangleSupport, packedRectangleSupport]
  have hcards := active_rectangle_diagonal_cards f.hs hL choice Finset.univ
  rw [hrect] at hcards
  have hchoiceTrue := fw_selected_choice_full_balance hnlo otherChoice true
  have hchoiceFalse := fw_selected_choice_full_balance hnlo otherChoice false
  have hmcount : (full ∩ mainCells n).card = 12 * (5 + 16 + 3 * (n / 450) + 238) := by
    rw [hm, hcards.1]
    simpa only [fwSelectedChoiceBlockCount] using hchoiceTrue
  have hacount : (full ∩ antiCells n).card = 12 * (5 + 16 + 3 * (n / 450) + 238) := by
    rw [ha, hcards.2]
    simpa only [fwSelectedChoiceBlockCount] using hchoiceFalse
  have hmsplit := Finset.card_sdiff_add_card_inter (mainCells n) full
  have hasplit := Finset.card_sdiff_add_card_inter (antiCells n) full
  rw [Finset.inter_comm, hmcount, mainCells_card] at hmsplit
  rw [Finset.inter_comm, hacount, antiCells_card] at hasplit
  refine ⟨hmcount, hacount, ?_, ?_⟩
  · change (mainCells n \ full).card = _
    exact Nat.eq_sub_of_add_eq hmsplit
  · change (antiCells n \ full).card = _
    exact Nat.eq_sub_of_add_eq hasplit

end
end Sude
