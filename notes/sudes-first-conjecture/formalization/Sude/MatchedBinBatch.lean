import Sude.MatchedBinBudget
import Sude.MatchedBinPlacementInterface
import Sude.DoublePairDepletionIteration

/-! Select a sequence of disjoint matched-bin blocks under one paid budget. -/
namespace Sude
noncomputable section

/-- The FW matched-bin stock and gap gate supply as many physically distinct
double blocks as fit the explicitly paid global deletion budget. Blocks
are valid over the actual bin unions and avoid the prior deleted entries.
The caller must establish the source-specific stocks, disjointness and gate. -/
theorem select_matched_bin_double_pairs {N W B X k : ℕ}
    (low high : Fin N → Finset ℕ) (removed differences : Finset ℕ)
    (hdis : (Set.univ : Set (Fin N × Bool)).PairwiseDisjoint
      (fun z => if z.2 then high z.1 else low z.1))
    (hlow : ∀ i, W ≤ (low i).card) (hhigh : ∀ i, W ≤ (high i).card)
    (horder : ∀ i j a, a ∈ low i → ∀ b, b ∈ high j → a < b)
    (hdiff : ∀ i a, a ∈ low i → ∀ b, b ∈ high i → b - a ∈ differences)
    (hspan : differences.card ≤ X)
    (hgate : (N : ℝ) * X < ((N * W - B : ℕ) : ℝ) ^ 2)
    (hbudget : removed.card + 4 * k ≤ B) :
    ∃ blocks : List DoublePair, blocks.length = k ∧
      (∀ b ∈ blocks, b.valid (Finset.univ.biUnion low) (Finset.univ.biUnion high)) ∧
      blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) ∧
      (∀ b ∈ blocks, Disjoint b.footprint removed) := by
  classical
  apply select_double_pairs_from_depletion_supply
    (fun b => b.valid (Finset.univ.biUnion low) (Finset.univ.biUnion high)) B k removed
  · intro R hR
    have hgateR := matched_bin_square_gate_of_budget R differences hR hspan hgate
    obtain ⟨b, hb⟩ := matched_bins_depleted_valid_block low high R differences
      hdis hlow hhigh horder hdiff hgateR
    let L := Finset.univ.biUnion (fun i => low i \ R)
    let H := Finset.univ.biUnion (fun i => high i \ R)
    have hLsub : L ⊆ Finset.univ.biUnion low := by
      intro x hx
      obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_biUnion.mpr ⟨i, hi, (Finset.mem_sdiff.mp hx).1⟩
    have hHsub : H ⊆ Finset.univ.biUnion high := by
      intro x hx
      obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_biUnion.mpr ⟨i, hi, (Finset.mem_sdiff.mp hx).1⟩
    have hdisR : Disjoint (L ∪ H) R := by
      apply Finset.disjoint_left.mpr
      intro x hx hxr
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hx
        exact (Finset.mem_sdiff.mp hx).2 hxr
      · obtain ⟨i, _, hx⟩ := Finset.mem_biUnion.mp hx
        exact (Finset.mem_sdiff.mp hx).2 hxr
    have hfoot : b.footprint ⊆ L ∪ H := by
      intro x hx
      simp only [DoublePair.footprint, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Finset.mem_union_left H hb.1
      · exact Finset.mem_union_left H hb.2.1
      · exact Finset.mem_union_right L hb.2.2.1
      · exact Finset.mem_union_right L hb.2.2.2.1
    exact ⟨b, DoublePair.valid_mono hb hLsub hHsub, Disjoint.mono_left hfoot hdisR⟩
  · exact hbudget

end
end Sude
