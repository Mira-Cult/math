import Sude.RectanglePairInvoice
import Sude.BridgeRectangleAllocation

/-! Actual diagonal incidences of both oriented pairs in a packed rectangle. -/
namespace Sude
noncomputable section

/-- Only the first endpoint of the first pair can meet the main diagonal,
and it does so precisely when that rectangle is designated for it. -/
theorem rectanglePairWeight_main {L n : ℕ} (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (j : Fin L) (pair : Fin 2) :
    rectanglePairWeight hs choice (fun c => c ∈ mainCells n) (j, pair) =
      if pair = 0 ∧ choice j = true then 1 else 0 := by
  have h01 := RectanglePacking.firstRow_secondColumn_off_diagonals hs hL choice j
  have h10 := RectanglePacking.secondRow_firstColumn_off_diagonals hs hL choice j
  have h11 := RectanglePacking.secondRow_secondColumn_off_diagonals hs hL choice j
  have hg := RectanglePacking.designated_corner_geometry hs choice j
  have hm : (RectanglePacking.firstRow hs j, RectanglePacking.firstColumn hs choice j) ∈ mainCells n ↔
      choice j = true := by
    cases hc : choice j
    · have hn := (hg.2 hc).2
      simp [hc, hn]
    · have hy := (hg.1 hc).1
      simp [hc, hy]
  fin_cases pair <;> cases hc : choice j <;>
    simp [rectanglePairWeight, prefixPairCorner, packedRectangleCorner, hc, hm,
      h01.1, h10.1, h11.1]

/-- Only the first endpoint of the first pair can meet the antidiagonal,
and it does so precisely when that rectangle is designated for it. -/
theorem rectanglePairWeight_anti {L n : ℕ} (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (j : Fin L) (pair : Fin 2) :
    rectanglePairWeight hs choice (fun c => c ∈ antiCells n) (j, pair) =
      if pair = 0 ∧ choice j = false then 1 else 0 := by
  have h01 := RectanglePacking.firstRow_secondColumn_off_diagonals hs hL choice j
  have h10 := RectanglePacking.secondRow_firstColumn_off_diagonals hs hL choice j
  have h11 := RectanglePacking.secondRow_secondColumn_off_diagonals hs hL choice j
  have hg := RectanglePacking.designated_corner_geometry hs choice j
  have ha : (RectanglePacking.firstRow hs j, RectanglePacking.firstColumn hs choice j) ∈ antiCells n ↔
      choice j = false := by
    cases hc : choice j
    · have hy := (hg.2 hc).1
      simp [hc, hy]
    · have hn := (hg.1 hc).2
      simp [hc, hn]
  fin_cases pair <;> cases hc : choice j <;>
    simp [rectanglePairWeight, prefixPairCorner, packedRectangleCorner, hc, ha,
      h01.2, h10.2, h11.2]

end
end Sude
