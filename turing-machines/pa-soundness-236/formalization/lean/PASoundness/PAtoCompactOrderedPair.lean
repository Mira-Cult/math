import PASoundness.HFCoding

/-! Standard HF Kuratowski pairs; no object-level K derivation is claimed. -/
namespace PASoundness.PAtoCompactOrderedPair
open PASoundness.HFCoding

def singleton (a : Object) : Object := assemble {a}
def unorderedPair (a b : Object) : Object := assemble {a,b}
def orderedPair (a b : Object) : Object := assemble {singleton a, unorderedPair a b}

@[simp] theorem mem_singleton (x a : Object) : x ∈ singleton a ↔ x = a := by
  simp [singleton]
@[simp] theorem mem_unorderedPair (x a b : Object) : x ∈ unorderedPair a b ↔ x = a ∨ x = b := by
  simp [unorderedPair]
@[simp] theorem mem_orderedPair (x a b : Object) : x ∈ orderedPair a b ↔
    x = singleton a ∨ x = unorderedPair a b := by
  simp [orderedPair]

/-- A diagonal Kuratowski pair determines both components. -/
theorem orderedPair_diag_unique (a b c : Object)
    (h : orderedPair a a = orderedPair b c) : a = b ∧ a = c := by
  have hs : unorderedPair a a = singleton a := by
    apply HFCoding.ext
    intro x
    simp
  have hbs : singleton b = singleton a := by
    have hm : singleton b ∈ orderedPair a a := by
      rw [h, mem_orderedPair]
      exact Or.inl rfl
    simpa [hs] using hm
  have hbc : unorderedPair b c = singleton a := by
    have hm : unorderedPair b c ∈ orderedPair a a := by
      rw [h, mem_orderedPair]
      exact Or.inr rfl
    simpa [hs] using hm
  have hab : b = a := by
    have hm : b ∈ singleton a := by rw [← hbs]; simp
    simpa using hm
  have hac : c = a := by
    have hm : c ∈ singleton a := by rw [← hbc]; simp
    simpa using hm
  exact ⟨hab.symm, hac.symm⟩

end PASoundness.PAtoCompactOrderedPair

#print axioms PASoundness.PAtoCompactOrderedPair.orderedPair_diag_unique
