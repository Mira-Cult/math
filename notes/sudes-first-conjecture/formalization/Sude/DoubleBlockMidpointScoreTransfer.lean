import Sude.DoubleBlockProtectedLogReallocation

/-! Source-reference-preserving transfer of a double-block midpoint score.
Physical pair coverage and any later flow action are separate obligations. -/
namespace Sude
noncomputable section

/-- Equal pair midpoints on the two current squares preserve every fixed-line
score, with exactly the same original source square for stage means. -/
theorem double_block_midpoint_score_transfer {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (source before after : Cell n ≃ Fin (n*n))
    (hmid : ∀ j b p, doubleBlockPairMidpoint cells after j b p =
      doubleBlockPairMidpoint cells before j b p) :
    doubleBlockActualCenteredScore cells line source after =
      doubleBlockActualCenteredScore cells line source before := by
  classical
  unfold doubleBlockActualCenteredScore
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [hmid]

end
end Sude
