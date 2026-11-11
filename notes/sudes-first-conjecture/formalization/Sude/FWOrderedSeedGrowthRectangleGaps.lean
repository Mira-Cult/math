import Sude.FWThetaFamilyWitness
import Sude.FWSeedOffsetActualDiagonal
import Sude.FWGrowthDiagonalPhysical

/-! Signed physical corner gaps in the ordered seed and growth rectangles. -/
namespace Sude
noncomputable section

/-- The two seed pairs keep their signed gap on the actual rectangle corners. -/
theorem fw_ordered_seed_rectangle_signed_gaps {n L : ℕ}
    {choice : Fin L → Bool} (f : FWThetaFamilyWitness n L choice)
    (j : Fin 16) (rect : Fin (4 * 6)) :
    let label := fwSeedRectangle f.hseedrect (finProdFinEquiv (j, rect))
    entry f.ordered (packedRectangleCorner f.hs choice (label, 1)) =
        entry f.ordered (packedRectangleCorner f.hs choice (label, 0)) + 2 ∧
    entry f.ordered (packedRectangleCorner f.hs choice (label, 2)) =
        entry f.ordered (packedRectangleCorner f.hs choice (label, 3)) + 2 := by
  have h0 := f.hseedgap j (prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (rect, 0))
  have h1 := f.hseedgap j (prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (rect, 1))
  rw [fw_seed_existing_rectangle_cell f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc j rect 0 true,
      fw_seed_existing_rectangle_cell f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc j rect 0 false] at h0
  rw [fw_seed_existing_rectangle_cell f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc j rect 1 true,
      fw_seed_existing_rectangle_cell f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc j rect 1 false] at h1
  exact ⟨by simpa [prefixPairCorner] using h0, by simpa [prefixPairCorner] using h1⟩

/-- Each growth rectangle has its own stage's signed pair gap on both pairs. -/
theorem fw_ordered_growth_rectangle_signed_gaps {n L : ℕ}
    {choice : Fin L → Bool} (f : FWThetaFamilyWitness n L choice)
    (j : Fin f.stages.length) (rect : Fin (4 * 6)) :
    let label := btGrowingOffsetRectangle
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) f.hoff (finProdFinEquiv (j, rect))
    entry f.ordered (packedRectangleCorner f.hs choice (label, 1)) =
        entry f.ordered (packedRectangleCorner f.hs choice (label, 0)) + (f.stages.get j).gap ∧
    entry f.ordered (packedRectangleCorner f.hs choice (label, 2)) =
        entry f.ordered (packedRectangleCorner f.hs choice (label, 3)) + (f.stages.get j).gap := by
  let offset := 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)
  have h0 := f.hpairgap j (prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (rect, 0))
  have h1 := f.hpairgap j (prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (rect, 1))
  rw [fw_growth_offset_rectangle_cell offset f.hoff f.hs choice f.gr f.gc f.hgr f.hgc j rect 0 true,
      fw_growth_offset_rectangle_cell offset f.hoff f.hs choice f.gr f.gc f.hgr f.hgc j rect 0 false] at h0
  rw [fw_growth_offset_rectangle_cell offset f.hoff f.hs choice f.gr f.gc f.hgr f.hgc j rect 1 true,
      fw_growth_offset_rectangle_cell offset f.hoff f.hs choice f.gr f.gc f.hgr f.hgc j rect 1 false] at h1
  exact ⟨by simpa [prefixPairCorner, offset] using h0, by simpa [prefixPairCorner, offset] using h1⟩

end
end Sude
