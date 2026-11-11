import Sude.FWSeedRectangleOffset
import Sude.DiagonalStageInvoice

/-! Exact diagonal incidence of the actual offset seed rectangles. -/
namespace Sude
noncomputable section

/-- The squared pair-incidence sum in one actual offset seed stage. -/
noncomputable def fwSeedOffsetRectangleStageInvoice {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (line : Cell n → Prop) (j : Fin 16) : ℝ :=
  ∑ rect : Fin (4 * 6), ∑ pair : Fin 2,
    (rectanglePairWeight hs choice line (fwSeedRectangle hseed (finProdFinEquiv (j, rect)), pair)) ^ 2

/-- Exactly twelve squared pair incidences lie on the main diagonal. -/
theorem fw_seed_offset_main_stage_invoice {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool) (j : Fin 16) :
    fwSeedOffsetRectangleStageInvoice hseed hs (fwBridgeSeedRectangleChoice hrect hseed otherChoice)
      (fun c => c ∈ mainCells n) j = 12 := by
  have hchoice : ∀ i : Fin (4 * 6), fwBridgeSeedRectangleChoice hrect hseed otherChoice
      (fwSeedRectangle hseed (finProdFinEquiv (j, i))) = decide (i.val < 2 * 6) := by
    intro i
    exact fwBridgeSeedRectangleChoice_seed hrect hseed otherChoice j i
  calc
    _ = (((Finset.univ : Finset (Fin (4 * 6))).filter fun i => i.val < 2 * 6).card : ℝ) := by
      simp only [fwSeedOffsetRectangleStageInvoice, Fin.sum_univ_two, rectanglePairWeight_main hs hL]
      simp [hchoice]
    _ = 12 := by
      rw [(bridgeDiagonal_index_counts 6).1]
      norm_num

/-- Exactly twelve squared pair incidences lie on the antidiagonal. -/
theorem fw_seed_offset_anti_stage_invoice {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool) (j : Fin 16) :
    fwSeedOffsetRectangleStageInvoice hseed hs (fwBridgeSeedRectangleChoice hrect hseed otherChoice)
      (fun c => c ∈ antiCells n) j = 12 := by
  have hchoice : ∀ i : Fin (4 * 6), fwBridgeSeedRectangleChoice hrect hseed otherChoice
      (fwSeedRectangle hseed (finProdFinEquiv (j, i))) = decide (i.val < 2 * 6) := by
    intro i
    exact fwBridgeSeedRectangleChoice_seed hrect hseed otherChoice j i
  calc
    _ = (((Finset.univ : Finset (Fin (4 * 6))).filter fun i => ¬ i.val < 2 * 6).card : ℝ) := by
      simp only [fwSeedOffsetRectangleStageInvoice, Fin.sum_univ_two, rectanglePairWeight_anti hs hL]
      simp [hchoice]
    _ = 12 := by
      rw [(bridgeDiagonal_index_counts 6).2]
      norm_num

end
end Sude
