import Sude.FWSeedPhysicalStageTotals

/-! Combine two supplied equal-quota physical pair families. No theta,
centering, numerical mean, or line-bound conclusion is asserted. -/
namespace Sude
noncomputable section

/-- Stage cells indexed by the disjoint union of the two stage families. -/
def combinedPhysicalPairStageCells {n A B Q : ℕ}
    (seed : (Fin A × Fin Q) × Bool → Cell n)
    (growth : (Fin B × Fin Q) × Bool → Cell n) : Fin A ⊕ Fin B → Finset (Cell n) :=
  Sum.elim (physicalPairStageCells seed) (physicalPairStageCells growth)

/-- The actual same-square average of the pair midpoints in one stage. -/
def physicalStageMidpointAverage {n P Q : ℕ}
    (a : Cell n ≃ Fin (n * n)) (cells : (Fin P × Fin Q) × Bool → Cell n)
    (j : Fin P) : ℝ :=
  (∑ i, (((entry a (cells ((j, i), false)) : ℝ) + entry a (cells ((j, i), true))) / 2)) / Q

/-- Reexpress the exact stage sum through its actual midpoint average. The
positive quota is needed only for the division defining the average. -/
theorem physical_pair_stage_sum_midpoint_average {n P Q : ℕ}
    (hQ : 0 < Q) (a : Cell n ≃ Fin (n * n))
    (cells : (Fin P × Fin Q) × Bool → Cell n) (hcells : Function.Injective cells)
    (j : Fin P) :
    (∑ c ∈ physicalPairStageCells cells j, (entry a c : ℝ)) =
      ((2 * Q : ℕ) : ℝ) * physicalStageMidpointAverage a cells j := by
  rw [physical_pair_stage_sum_midpoints a cells hcells
    (fun j i => (((entry a (cells ((j, i), false)) : ℝ) + entry a (cells ((j, i), true))) / 2))
    (by intro j i; rfl) j]
  unfold physicalStageMidpointAverage
  have hQ' : (Q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ)
  push_cast
  field_simp

/-- Supplied injective pair maps with disjoint physical images form one
pairwise-disjoint stage family. Each stage contains exactly `2Q` cells, has
the exact same-square midpoint-average sum, and lies inside `roles`. -/
theorem combined_physical_stage_family {n A B Q : ℕ} (hQ : 0 < Q)
    (a : Cell n ≃ Fin (n * n)) (roles : Finset (Cell n))
    (seed : (Fin A × Fin Q) × Bool → Cell n)
    (growth : (Fin B × Fin Q) × Bool → Cell n)
    (hseed : Function.Injective seed) (hgrowth : Function.Injective growth)
    (hsep : Disjoint (Finset.univ.image seed) (Finset.univ.image growth))
    (hseedRoles : Finset.univ.image seed ⊆ roles)
    (hgrowthRoles : Finset.univ.image growth ⊆ roles) :
    let cells := combinedPhysicalPairStageCells seed growth
    let means := Sum.elim (physicalStageMidpointAverage a seed) (physicalStageMidpointAverage a growth)
    Set.PairwiseDisjoint (Set.univ : Set (Fin A ⊕ Fin B)) cells ∧
    (∀ j, (cells j).card = 2 * Q) ∧
    (∀ j, (∑ c ∈ cells j, (entry a c : ℝ)) = ((2 * Q : ℕ) : ℝ) * means j) ∧
    (∀ S : Finset (Fin A ⊕ Fin B), S.biUnion cells ⊆ roles) := by
  classical
  dsimp only
  have hseedStage := physical_pair_stage_cells_disjoint_card seed hseed
  have hgrowthStage := physical_pair_stage_cells_disjoint_card growth hgrowth
  have hseedSub (j : Fin A) : physicalPairStageCells seed j ⊆ Finset.univ.image seed := by
    intro c hc
    obtain ⟨⟨i, side⟩, _, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_image.mpr ⟨((j, i), side), Finset.mem_univ _, rfl⟩
  have hgrowthSub (j : Fin B) : physicalPairStageCells growth j ⊆ Finset.univ.image growth := by
    intro c hc
    obtain ⟨⟨i, side⟩, _, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_image.mpr ⟨((j, i), side), Finset.mem_univ _, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j _ k _ hjk
    rcases j with j | j <;> rcases k with k | k
    · exact hseedStage.1 (Set.mem_univ j) (Set.mem_univ k) (fun h => hjk (congrArg Sum.inl h))
    · exact hsep.mono (hseedSub j) (hgrowthSub k)
    · exact (hsep.mono (hseedSub k) (hgrowthSub j)).symm
    · exact hgrowthStage.1 (Set.mem_univ j) (Set.mem_univ k) (fun h => hjk (congrArg Sum.inr h))
  · intro j
    rcases j with j | j
    · exact hseedStage.2 j
    · exact hgrowthStage.2 j
  · intro j
    rcases j with j | j
    · exact physical_pair_stage_sum_midpoint_average hQ a seed hseed j
    · exact physical_pair_stage_sum_midpoint_average hQ a growth hgrowth j
  · intro S c hc
    obtain ⟨j, hj, hc⟩ := Finset.mem_biUnion.mp hc
    rcases j with j | j
    · exact hseedRoles (hseedSub j hc)
    · exact hgrowthRoles (hgrowthSub j hc)

end
end Sude
