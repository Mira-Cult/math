import Sude.MatchedBinDepletedPairs
import Sude.DoublePairPlacement

/-! Connect the FW matched-bin result to the existing physical block interface. -/
namespace Sude
noncomputable section

/-- The surviving repeated-gap block satisfies the existing `DoublePair.valid`
interface over the unions of the actual surviving bins. Thus it can be used
by physical placement lemmas once their cell and pool hypotheses are proved. -/
theorem matched_bins_depleted_valid_block {N W : ℕ}
    (low high : Fin N → Finset ℕ) (removed differences : Finset ℕ)
    (hdis : (Set.univ : Set (Fin N × Bool)).PairwiseDisjoint
      (fun k => if k.2 then high k.1 else low k.1))
    (hlow : ∀ i, W ≤ (low i).card) (hhigh : ∀ i, W ≤ (high i).card)
    (horder : ∀ i j a, a ∈ low i → ∀ b, b ∈ high j → a < b)
    (hdiff : ∀ i a, a ∈ low i → ∀ b, b ∈ high i → b - a ∈ differences)
    (hgate : (N : ℝ) * differences.card < ((N * W - removed.card : ℕ) : ℝ) ^ 2) :
    ∃ b : DoublePair, b.valid
      (Finset.univ.biUnion (fun i => low i \ removed))
      (Finset.univ.biUnion (fun i => high i \ removed)) := by
  classical
  obtain ⟨b, ⟨i, hli, hhi⟩, ⟨j, hlj, hhj⟩,
      hlowne, hhighne, ho₁, ho₂, _, _, hgap⟩ :=
    matched_bins_repeated_after_deletion low high removed differences hdis hlow hhigh horder hdiff hgate
  refine ⟨b, ?_, ?_, ?_, ?_, hlowne, hhighne, ho₁, ho₂, hgap⟩
  · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hli⟩
  · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hlj⟩
  · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hhi⟩
  · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hhj⟩

end
end Sude
