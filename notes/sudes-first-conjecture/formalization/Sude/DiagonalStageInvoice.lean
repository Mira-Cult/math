import Sude.RectangleDiagonalIncidence
import Sude.PrefixStageInvoice

/-! Exact diagonal rectangle incidence invoice at each selected stage. -/
namespace Sude
noncomputable section

/-- With the source's diagonal choices, each stage has exactly `2d` squared
rectangle-pair incidences on the main diagonal. -/
theorem prefixRectangle_main_stage_invoice {P d L n : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L)
    (otherChoice : Fin L → Bool) (j : Fin P) :
    prefixRectangleStageInvoice hrect hs (bridgeDiagonalChoice hrect otherChoice)
      (fun c => c ∈ mainCells n) j = 2 * (d : ℝ) := by
  have hchoice : ∀ i : Fin (4 * d), bridgeDiagonalChoice hrect otherChoice
      (Fin.castLE hrect (finProdFinEquiv (j, i))) = decide (i.val < 2 * d) := by
    intro i
    simpa [bridgeDiagonalRectangle] using bridgeDiagonalChoice_at hrect otherChoice j i
  calc
    _ = (((Finset.univ : Finset (Fin (4 * d))).filter fun i => i.val < 2 * d).card : ℝ) := by
      simp only [prefixRectangleStageInvoice, prefixRectanglePairSlot, Fin.sum_univ_two,
        rectanglePairWeight_main hs hL]
      simp [hchoice]
    _ = 2 * (d : ℝ) := by
      rw [(bridgeDiagonal_index_counts d).1]
      push_cast
      ring

/-- The other `2d` stage rectangles give exactly the same invoice on the
antidiagonal, with no assumption that the two labelled lines are distinct. -/
theorem prefixRectangle_anti_stage_invoice {P d L n : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L)
    (otherChoice : Fin L → Bool) (j : Fin P) :
    prefixRectangleStageInvoice hrect hs (bridgeDiagonalChoice hrect otherChoice)
      (fun c => c ∈ antiCells n) j = 2 * (d : ℝ) := by
  have hchoice : ∀ i : Fin (4 * d), bridgeDiagonalChoice hrect otherChoice
      (Fin.castLE hrect (finProdFinEquiv (j, i))) = decide (i.val < 2 * d) := by
    intro i
    simpa [bridgeDiagonalRectangle] using bridgeDiagonalChoice_at hrect otherChoice j i
  calc
    _ = (((Finset.univ : Finset (Fin (4 * d))).filter fun i => ¬ i.val < 2 * d).card : ℝ) := by
      simp only [prefixRectangleStageInvoice, prefixRectanglePairSlot, Fin.sum_univ_two,
        rectanglePairWeight_anti hs hL]
      simp [hchoice]
    _ = 2 * (d : ℝ) := by
      rw [(bridgeDiagonal_index_counts d).2]
      push_cast
      ring

end
end Sude
