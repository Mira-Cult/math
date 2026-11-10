import PASoundness.PAtoCompactOrderedPair

/-! Standard HF Kuratowski-pair injectivity. This is metatheoretic semantic
support for the candidate graph representation, not a K derivation. -/
namespace PASoundness.PAtoCompactOrderedPairInjectivity
open PASoundness.HFCoding PASoundness.PAtoCompactOrderedPair

theorem orderedPair_injective (a b c d : Object)
    (h : orderedPair a b = orderedPair c d) : a = c ∧ b = d := by
  have hsing : singleton a = singleton c ∨ singleton a = unorderedPair c d := by
    have hm : singleton a ∈ orderedPair c d := by
      rw [← h, mem_orderedPair]
      exact Or.inl rfl
    simpa only [mem_orderedPair] using hm
  have hac : a = c := by
    rcases hsing with hsc | hsc
    · have hm : c ∈ singleton a := by rw [hsc]; simp
      have hca : c = a := (mem_singleton _ _).mp hm
      exact hca.symm
    · have hm : c ∈ singleton a := by rw [hsc]; simp
      have hca : c = a := (mem_singleton _ _).mp hm
      exact hca.symm
  subst c
  have hpair : unorderedPair a b = singleton a ∨ unorderedPair a b = unorderedPair a d := by
    have hm : unorderedPair a b ∈ orderedPair a d := by
      rw [← h, mem_orderedPair]
      exact Or.inr rfl
    simpa only [mem_orderedPair] using hm
  constructor
  · rfl
  · rcases hpair with hs | hs
    · have hb : b = a := by
        have hm : b ∈ singleton a := by rw [← hs]; simp
        exact (mem_singleton _ _).mp hm
      subst b
      exact (orderedPair_diag_unique a a d h).2
    · have hb : b = a ∨ b = d := by
        have hm : b ∈ unorderedPair a d := by rw [← hs]; simp
        exact (mem_unorderedPair _ _ _).mp hm
      have hd : d = a ∨ d = b := by
        have hm : d ∈ unorderedPair a b := by rw [hs]; simp
        exact (mem_unorderedPair _ _ _).mp hm
      rcases hb with hb | hb
      · rcases hd with hd | hd
        · exact hb.trans hd.symm
        · exact hd.symm
      · exact hb

end PASoundness.PAtoCompactOrderedPairInjectivity

#print axioms PASoundness.PAtoCompactOrderedPairInjectivity.orderedPair_injective
