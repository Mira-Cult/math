import Sude.DoublePairPlacement
import Sude.BridgeDepletion

/-! Set coverage of the endpoints of an arbitrary double-pair list. -/
namespace Sude
noncomputable section

/-- Enumerating four endpoints for every list position gives exactly the
union of the batch's low and high endpoint sets. Repeated blocks or endpoints
are allowed, and the empty list is included. -/
theorem double_pair_sequence_endpoint_image (blocks : List DoublePair) :
    (Finset.univ : Finset (Fin blocks.length × Fin 4)).image
      (doublePairSequenceEndpoint blocks) = doubleBatchLow blocks ∪ doubleBatchHigh blocks := by
  classical
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, doubleBatchLow, doubleBatchHigh,
    Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨i, j⟩, hj⟩
    have hi := List.get_mem blocks i
    fin_cases j <;> simp [doublePairSequenceEndpoint, DoublePair.endpoint] at hj
    · exact Or.inl ⟨_, hi, Or.inl hj.symm⟩
    · exact Or.inr ⟨_, hi, Or.inl hj.symm⟩
    · exact Or.inr ⟨_, hi, Or.inr hj.symm⟩
    · exact Or.inl ⟨_, hi, Or.inr hj.symm⟩
  · rintro (⟨b, hb, h⟩ | ⟨b, hb, h⟩)
    all_goals obtain ⟨i, hi⟩ := List.get_of_mem hb
    all_goals simp only [List.get_eq_getElem] at hi
    · rcases h with h | h
      · exact ⟨(i, 0), by simpa [doublePairSequenceEndpoint, DoublePair.endpoint, hi] using h.symm⟩
      · exact ⟨(i, 3), by simpa [doublePairSequenceEndpoint, DoublePair.endpoint, hi] using h.symm⟩
    · rcases h with h | h
      · exact ⟨(i, 1), by simpa [doublePairSequenceEndpoint, DoublePair.endpoint, hi] using h.symm⟩
      · exact ⟨(i, 2), by simpa [doublePairSequenceEndpoint, DoublePair.endpoint, hi] using h.symm⟩

end
end Sude
