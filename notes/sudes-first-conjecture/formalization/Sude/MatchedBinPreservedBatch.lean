import Sude.MatchedBinBudget
import Sude.DoublePairDepletionIteration

/-! Preserve each cross-pair's matched-bin label through batch selection. -/
namespace Sude
noncomputable section

/-- Both cross-pairs are valid over the bin unions, and each low/high pair
comes from one common bin. The two pairs may use different bins. -/
def DoublePair.MatchedValid {N : ℕ} (block : DoublePair)
    (low high : Fin N → Finset ℕ) : Prop :=
  block.valid (Finset.univ.biUnion low) (Finset.univ.biUnion high) ∧
  (∃ i, block.low₁ ∈ low i ∧ block.high₁ ∈ high i) ∧
  (∃ j, block.low₂ ∈ low j ∧ block.high₂ ∈ high j)

/-- The matched-bin square gate selects a disjoint block sequence without
forgetting the bin label of either pair. -/
theorem select_matched_bin_double_pairs_preserving_labels {N W B X k : ℕ}
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
      (∀ b ∈ blocks, b.MatchedValid low high) ∧
      blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) ∧
      (∀ b ∈ blocks, Disjoint b.footprint removed) := by
  classical
  apply select_double_pairs_from_depletion_supply (fun b => b.MatchedValid low high) B k removed
  · intro R hR
    have hgateR := matched_bin_square_gate_of_budget R differences hR hspan hgate
    obtain ⟨block, ⟨i, hli, hhi⟩, ⟨j, hlj, hhj⟩,
      hlowne, hhighne, ho₁, ho₂, _, _, hgap⟩ :=
      matched_bins_repeated_after_deletion low high R differences hdis hlow hhigh horder hdiff hgateR
    have hli' := Finset.mem_sdiff.mp hli
    have hhi' := Finset.mem_sdiff.mp hhi
    have hlj' := Finset.mem_sdiff.mp hlj
    have hhj' := Finset.mem_sdiff.mp hhj
    have hv : block.valid (Finset.univ.biUnion low) (Finset.univ.biUnion high) := by
      refine ⟨?_, ?_, ?_, ?_, hlowne, hhighne, ho₁, ho₂, hgap⟩
      · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hli'.1⟩
      · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hlj'.1⟩
      · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hhi'.1⟩
      · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hhj'.1⟩
    have havoid : Disjoint block.footprint R := by
      apply Finset.disjoint_left.mpr
      intro x hx hxr
      simp only [DoublePair.footprint, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hli'.2 hxr
      · exact hlj'.2 hxr
      · exact hhi'.2 hxr
      · exact hhj'.2 hxr
    exact ⟨block, ⟨hv, ⟨i, hli'.1, hhi'.1⟩, ⟨j, hlj'.1, hhj'.1⟩⟩, havoid⟩
  · exact hbudget

end
end Sude
