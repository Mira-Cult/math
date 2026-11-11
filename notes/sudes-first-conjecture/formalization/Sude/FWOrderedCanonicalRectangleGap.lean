import Sude.FWOrderedActiveRectangleGaps

/-! A canonical signed gap on the supplied ordered square. It carries no grid,
radius, spare-label, CY, or prime assertion. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The natural difference of the first oriented pair on a rectangle. -/
def fwOrderedCanonicalRectangleGap {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) (i : Fin L) : ℕ :=
  entry f.ordered (packedRectangleCorner f.hs choice (i,1)) -
    entry f.ordered (packedRectangleCorner f.hs choice (i,0))

/-- The canonical physical gap matches all four stage families and satisfies
both signed corner equations on the exact active labels. -/
theorem fw_ordered_canonical_rectangle_gap {n : ℕ}
    {choice : Fin (fwJointRectangleCount n 254) → Bool}
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice) :
    (∀ (j : Fin 5) (r : Fin (4*6)),
      fwOrderedCanonicalRectangleGap f (bridgeDiagonalRectangle f.hrect (finProdFinEquiv (j,r))) =
        f.gapb j (Fin.castLE (by omega : 4*6 ≤ 3*(n+8)) r)) ∧
    (∀ (j : Fin 16) (r : Fin (4*6)),
      fwOrderedCanonicalRectangleGap f (fwSeedRectangle f.hseedrect (finProdFinEquiv (j,r))) = 2) ∧
    (∀ (j : Fin (3*(n/450))) (r : Fin (4*6)),
      fwOrderedCanonicalRectangleGap f (fwWideRectangle f.hwide (finProdFinEquiv (j,r))) =
        f.gapw j (Fin.castLE (by omega : 4*6 ≤ 3*(n+8)) r)) ∧
    (∀ (j : Fin f.stages.length) (r : Fin (4*6)),
      fwOrderedCanonicalRectangleGap f (btGrowingOffsetRectangle
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) f.hoff (finProdFinEquiv (j,r))) =
        (f.stages.get j).gap) ∧
    (∀ i ∈ fwActiveRectangleLabels n f.stages.length f.stageCap,
      entry f.ordered (packedRectangleCorner f.hs choice (i,1)) =
        entry f.ordered (packedRectangleCorner f.hs choice (i,0)) + fwOrderedCanonicalRectangleGap f i ∧
      entry f.ordered (packedRectangleCorner f.hs choice (i,2)) =
        entry f.ordered (packedRectangleCorner f.hs choice (i,3)) + fwOrderedCanonicalRectangleGap f i) := by
  have hb : ∀ (j : Fin 5) (r : Fin (4*6)),
      fwOrderedCanonicalRectangleGap f (bridgeDiagonalRectangle f.hrect (finProdFinEquiv (j,r))) =
        f.gapb j (Fin.castLE (by omega : 4*6 ≤ 3*(n+8)) r) := by
    intro j r
    have h := (fw_ordered_bridge_rectangle_gaps f j r).1
    simp only [fwOrderedCanonicalRectangleGap, h, Nat.add_sub_cancel_left]
  have hs : ∀ (j : Fin 16) (r : Fin (4*6)),
      fwOrderedCanonicalRectangleGap f (fwSeedRectangle f.hseedrect (finProdFinEquiv (j,r))) = 2 := by
    intro j r
    have h := (fw_ordered_seed_rectangle_signed_gaps f j r).1
    simp only [fwOrderedCanonicalRectangleGap, h, Nat.add_sub_cancel_left]
  have hw : ∀ (j : Fin (3*(n/450))) (r : Fin (4*6)),
      fwOrderedCanonicalRectangleGap f (fwWideRectangle f.hwide (finProdFinEquiv (j,r))) =
        f.gapw j (Fin.castLE (by omega : 4*6 ≤ 3*(n+8)) r) := by
    intro j r
    have h := (fw_ordered_wide_rectangle_gaps f j r).1
    simp only [fwOrderedCanonicalRectangleGap, h, Nat.add_sub_cancel_left]
  have hg : ∀ (j : Fin f.stages.length) (r : Fin (4*6)),
      fwOrderedCanonicalRectangleGap f (btGrowingOffsetRectangle
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) f.hoff (finProdFinEquiv (j,r))) =
        (f.stages.get j).gap := by
    intro j r
    have h := (fw_ordered_growth_rectangle_signed_gaps f j r).1
    simp only [fwOrderedCanonicalRectangleGap, h, Nat.add_sub_cancel_left]
  exact ⟨hb, hs, hw, hg, fw_ordered_active_rectangle_signed_gaps f _ hb hs hw hg⟩

end
end Sude
