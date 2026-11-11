import Sude.DoubleBlockScoreDecomposition

/-! Exact source-stage midpoint mean preservation under the supplied
block permutations and pair swaps. No concentration or allocation is asserted. -/
namespace Sude
noncomputable section

/-- Side-preserving double-block reallocation preserves the sum of the actual
pair midpoints in each stage and its block-midpoint mean, including an empty
block index type. This follows from the explicit pair grouping, not merely
from equality of the endpoint value sets. -/
theorem double_block_stage_midpoint_mean_preserved {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (old new : Cell n ≃ Fin (n*n))
    (π : Fin P → Equiv.Perm (Fin B)) (swap : Fin P → Fin B → Bool)
    (hentry : ∀ j b p side, entry new (cells ((j,b,p),side)) =
      entry old (cells ((j,π j b, doubleBlockPairSwap (swap j b) p),side)))
    (j : Fin P) :
    (∑ b, ∑ p, doubleBlockPairMidpoint cells new j b p) =
      ∑ b, ∑ p, doubleBlockPairMidpoint cells old j b p ∧
    doubleStageMidpointMean cells new j = doubleStageMidpointMean cells old j := by
  classical
  have hmid (b : Fin B) (p : Fin 2) :
      doubleBlockPairMidpoint cells new j b p =
        doubleBlockPairMidpoint cells old j (π j b) (doubleBlockPairSwap (swap j b) p) := by
    simp only [doubleBlockPairMidpoint, hentry]
  have hsum : (∑ b, ∑ p, doubleBlockPairMidpoint cells new j b p) =
      ∑ b, ∑ p, doubleBlockPairMidpoint cells old j b p := by
    calc
      _ = ∑ b, ∑ p, doubleBlockPairMidpoint cells old j (π j b) (doubleBlockPairSwap (swap j b) p) := by
        apply Finset.sum_congr rfl
        intro b _
        exact Finset.sum_congr rfl (fun p _ => hmid b p)
      _ = ∑ b, ∑ p, doubleBlockPairMidpoint cells old j (π j b) p := by
        apply Finset.sum_congr rfl
        intro b _
        exact Equiv.sum_comp (doubleBlockPairSwap (swap j b)) (doubleBlockPairMidpoint cells old j (π j b))
      _ = _ := Equiv.sum_comp (π j) (fun b => ∑ p, doubleBlockPairMidpoint cells old j b p)
  refine ⟨hsum, ?_⟩
  have hblocks : (∑ b, doubleBlockMidpoint cells new j b) = ∑ b, doubleBlockMidpoint cells old j b := by
    simp only [Fin.sum_univ_two, Finset.sum_add_distrib] at hsum
    simp only [doubleBlockMidpoint]
    rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib]
    linarith
  simp only [doubleStageMidpointMean, hblocks]

/-- The same conclusion holds simultaneously for supplied bridge and wide
physical maps, each with its own stage-wise block permutation and swap. -/
theorem double_block_bridge_wide_stage_means_preserved {n P W B : ℕ}
    (bridge : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (wide : (Fin W × Fin B × Fin 2) × Bool → Cell n)
    (old new : Cell n ≃ Fin (n*n))
    (πb : Fin P → Equiv.Perm (Fin B)) (sb : Fin P → Fin B → Bool)
    (πw : Fin W → Equiv.Perm (Fin B)) (sw : Fin W → Fin B → Bool)
    (hbridge : ∀ j b p side, entry new (bridge ((j,b,p),side)) =
      entry old (bridge ((j,πb j b, doubleBlockPairSwap (sb j b) p),side)))
    (hwide : ∀ j b p side, entry new (wide ((j,b,p),side)) =
      entry old (wide ((j,πw j b, doubleBlockPairSwap (sw j b) p),side))) :
    (∀ j, doubleStageMidpointMean bridge new j = doubleStageMidpointMean bridge old j) ∧
    (∀ j, doubleStageMidpointMean wide new j = doubleStageMidpointMean wide old j) := by
  exact ⟨fun j => (double_block_stage_midpoint_mean_preserved bridge old new πb sb hbridge j).2,
    fun j => (double_block_stage_midpoint_mean_preserved wide old new πw sw hwide j).2⟩

end
end Sude
