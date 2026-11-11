import Sude.ActualUnusedPool
import Sude.PrimeIndex

/-! Every subset of the prescribed pool has strict width below its maximum. -/
namespace Sude
noncomputable section

/-- This strict bound applies to the exact unused stock for every reservation
and uses only the prescribed pool, without any external prime estimate. -/
theorem actual_unused_pool_strict_width {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) :
    ∀ u ∈ actualUnusedPool a reserved, ∀ v ∈ actualUnusedPool a reserved,
      (u.val : ℝ) - (v.val : ℝ) < (poolMaximum n : ℝ) := by
  intro u _ v _
  have hu : (u.val : ℝ) ≤ poolMaximum n := by exact_mod_cast pool_le_poolMaximum u.property
  have hp : Nat.Prime v.val := by
    obtain ⟨i, hi⟩ := v.property
    rw [← hi]
    exact Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (i.val + 1)
  have hv : (0 : ℝ) < v.val := by exact_mod_cast hp.pos
  linarith

end
end Sude
