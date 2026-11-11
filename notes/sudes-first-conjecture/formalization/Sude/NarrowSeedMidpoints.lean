import Sude.NarrowSeedPhysical

/-! Relate sorted seed lower endpoints to actual pair midpoint ranges. -/
namespace Sude
noncomputable section

/-- The real midpoint of the two actual entries of one sorted pair. -/
def sortedSeedMidpoint (candidates : Finset ℕ) (r Q gap : ℕ)
    (hcard : candidates.card = r * Q) (j : Fin r) (i : Fin Q) : ℝ :=
  ((sortedSeedEndpoint candidates r Q gap hcard ((j, i), false) : ℝ) +
    (sortedSeedEndpoint candidates r Q gap hcard ((j, i), true) : ℝ)) / 2

theorem sortedSeedMidpoint_slot (candidates : Finset ℕ) (r Q gap : ℕ)
    (hcard : candidates.card = r * Q) (j : Fin r) (i : Fin Q) :
    sortedSeedMidpoint candidates r Q gap hcard j i =
      sortedSeedReal candidates r Q hcard (j.val * Q + i.val) + (gap : ℝ) / 2 := by
  rw [sortedSeedReal_slot]
  simp [sortedSeedMidpoint, sortedSeedEndpoint, pairEndpoint]
  ring

/-- The width used in the NS variance bound is exactly the span between
actual pair midpoints at the first and last slots of the sorted group. -/
theorem sortedSeedMidpoint_range (candidates : Finset ℕ) (r Q gap : ℕ)
    (hcard : candidates.card = r * Q) (hQ : 0 < Q) (j : Fin r) :
    sortedSeedMidpoint candidates r Q gap hcard j ⟨Q - 1, by omega⟩ -
      sortedSeedMidpoint candidates r Q gap hcard j ⟨0, hQ⟩ =
    sortedSeedReal candidates r Q hcard (j.val * Q + (Q - 1)) -
      sortedSeedReal candidates r Q hcard (j.val * Q) := by
  rw [sortedSeedMidpoint_slot, sortedSeedMidpoint_slot]
  simp only [Nat.add_zero]
  ring

end
end Sude
