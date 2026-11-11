import Sude.ActiveRectangleDiagonalGeometry
import Sude.FWSelectedSpareChoiceCount
import Sude.SpareRectangleLineSeparation
import Sude.FWPhysicalPrefixMeanOfTheta

/-! Coarse spare diagonal comparison on one supplied physical square.
The geometric count uses the selected choice for every potential growth stage;
no spare value balance, complete-diagonal overlap, or prime is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The actual spare reservation contributes equally many cells to each
physical diagonal. Pool range bounds the difference of their two sums, on the
same supplied square, by the number of corners on either side times X. -/
theorem fw_selected_spare_diagonal_bound {n P : ℕ} (hnlo : 19485 ≤ n) (hP : P ≤ 238)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) :
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let spare := packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
    (spare ∩ mainCells n).card = 12*(238-P) ∧
    (spare ∩ antiCells n).card = 12*(238-P) ∧
    |(∑ z ∈ spare ∩ mainCells n, (entry a z : ℝ)) -
      (∑ z ∈ spare ∩ antiCells n, (entry a z : ℝ))| ≤
        ((12*(238-P) : ℕ) : ℝ) * (poolMaximum n : ℝ) := by
  classical
  dsimp only
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let labels := fwSpareRectangleLabels n P hP
  let spare := packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
  have hspare : spare = activeRectangleSupport hs choice labels := by
    exact (fw_spare_rectangle_line_separation hP hs choice).2.2.2
  have hL : 3 ≤ fwJointRectangleCount n 254 := by simp [fwJointRectangleCount]; omega
  have hc := active_rectangle_diagonal_cards hs hL choice labels
  have hmcard : (spare ∩ mainCells n).card = 12*(238-P) := by
    rw [hspare, hc.1]
    exact fw_selected_spare_choice_count hnlo hP otherChoice true
  have hacard : (spare ∩ antiCells n).card = 12*(238-P) := by
    rw [hspare, hc.2]
    exact fw_selected_spare_choice_count hnlo hP otherChoice false
  have hsum (T : Finset (Cell n)) :
      0 ≤ ∑ z ∈ T, (entry a z : ℝ) ∧
      (∑ z ∈ T, (entry a z : ℝ)) ≤ (T.card : ℝ) * (poolMaximum n : ℝ) := by
    constructor
    · exact Finset.sum_nonneg (fun z _ => (physical_entry_pool_range a z).1)
    · calc
        _ ≤ ∑ _z ∈ T, (poolMaximum n : ℝ) :=
          Finset.sum_le_sum (fun z _ => (physical_entry_pool_range a z).2)
        _ = (T.card : ℝ) * (poolMaximum n : ℝ) := by simp
  have hm := hsum (spare ∩ mainCells n)
  have ha := hsum (spare ∩ antiCells n)
  rw [hmcard] at hm
  rw [hacard] at ha
  refine ⟨hmcard, hacard, ?_⟩
  apply abs_le.mpr
  constructor <;> linarith

end
end Sude
