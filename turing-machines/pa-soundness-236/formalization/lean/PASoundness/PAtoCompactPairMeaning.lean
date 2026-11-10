import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactOrderedPair

/-! Standard HF semantics of the candidate relational Kuratowski-pair
formula. These results are external semantic checks, not K derivations. -/
namespace PASoundness.PAtoCompactPairMeaning
open PASoundness.CompactNamed PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.CompactMatrix (Environment bit update)
open PASoundness.HFCoding PASoundness.PAtoCompactOrderedPair

private def both' (a b : Formula) : Formula := (a.imp b.not).not
private def either' (a b : Formula) : Formula := a.not.imp b
private def iff' (a b : Formula) : Formula := both' (a.imp b) (b.imp a)

/-- Exact standard semantics of the literal named pair relation, provided its
three visible names do not collide with the internal binders. -/
theorem pairFormula_semantics (p a b : Nat) (ρ : Environment)
    (hp : p ≠ 20 ∧ p ≠ 21 ∧ p ≠ 22)
    (ha : a ≠ 20 ∧ a ≠ 21 ∧ a ≠ 22)
    (hb : b ≠ 20 ∧ b ≠ 21 ∧ b ≠ 22) :
    (pairFormula p a b).Realize ρ ↔
      ∃ s t, (∀ v, bit s v = true ↔ v = ρ a) ∧
        (∀ v, bit t v = true ↔ v = ρ a ∨ v = ρ b) ∧
        (∀ v, bit (ρ p) v = true ↔ v = s ∨ v = t) := by
  classical
  have he : pairFormula p a b = .ex 20 (.ex 21 (both'
    (.all 22 (iff' (.member 20 22) (.equal 22 a)))
    (both' (.all 22 (iff' (.member 21 22) (either' (.equal 22 a) (.equal 22 b))))
      (.all 22 (iff' (.member p 22) (either' (.equal 22 20) (.equal 22 21))))))) := rfl
  rw [he]
  simp [both', iff', either', Formula.Realize, Formula.not, update,
    hp.1, hp.2.1, hp.2.2, ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2,
    or_iff_not_imp_left, iff_def]

/-- In standard HF, the relational pair formula denotes the canonical
Kuratowski pair. This is a semantic theorem, not a K proof of extensionality. -/
theorem pairFormula_realize_iff (p a b : Nat) (ρ : Environment)
    (hp : p ≠ 20 ∧ p ≠ 21 ∧ p ≠ 22)
    (ha : a ≠ 20 ∧ a ≠ 21 ∧ a ≠ 22)
    (hb : b ≠ 20 ∧ b ≠ 21 ∧ b ≠ 22) :
    (pairFormula p a b).Realize ρ ↔
      (orderedPair ⟨ρ a⟩ ⟨ρ b⟩).code = ρ p := by
  have eq_code (v : Nat) (x : Object) : (⟨v⟩ : Object) = x ↔ v = x.code := by
    constructor
    · intro h; exact congrArg Object.code h
    · intro h; exact HFCoding.code_injective h
  rw [pairFormula_semantics p a b ρ hp ha hb]
  constructor
  · rintro ⟨s,t,hs,ht,hpair⟩
    have hs' : (⟨s⟩ : Object) = PAtoCompactOrderedPair.singleton ⟨ρ a⟩ := by
      apply HFCoding.ext
      rintro ⟨v⟩
      change bit s v = true ↔ (⟨v⟩ : Object) ∈ PAtoCompactOrderedPair.singleton ⟨ρ a⟩
      simpa only [mem_singleton, Object.mk.injEq] using hs v
    have ht' : (⟨t⟩ : Object) = unorderedPair ⟨ρ a⟩ ⟨ρ b⟩ := by
      apply HFCoding.ext
      rintro ⟨v⟩
      change bit t v = true ↔ (⟨v⟩ : Object) ∈ unorderedPair ⟨ρ a⟩ ⟨ρ b⟩
      simpa only [mem_unorderedPair, Object.mk.injEq] using ht v
    have hp' : (⟨ρ p⟩ : Object) = orderedPair ⟨ρ a⟩ ⟨ρ b⟩ := by
      apply HFCoding.ext
      rintro ⟨v⟩
      change bit (ρ p) v = true ↔ (⟨v⟩ : Object) ∈ orderedPair ⟨ρ a⟩ ⟨ρ b⟩
      simpa only [mem_orderedPair, ← hs', ← ht', Object.mk.injEq] using hpair v
    exact (congrArg Object.code hp').symm
  · intro he
    refine ⟨(PAtoCompactOrderedPair.singleton ⟨ρ a⟩).code, (unorderedPair ⟨ρ a⟩ ⟨ρ b⟩).code, ?_, ?_, ?_⟩
    · intro v
      change (⟨v⟩ : Object) ∈ PAtoCompactOrderedPair.singleton ⟨ρ a⟩ ↔ _
      simp only [mem_singleton, Object.mk.injEq]
    · intro v
      change (⟨v⟩ : Object) ∈ unorderedPair ⟨ρ a⟩ ⟨ρ b⟩ ↔ _
      simp only [mem_unorderedPair, Object.mk.injEq]
    · intro v
      rw [← he]
      change (⟨v⟩ : Object) ∈ orderedPair ⟨ρ a⟩ ⟨ρ b⟩ ↔ _
      simp only [mem_orderedPair, eq_code]

end PASoundness.PAtoCompactPairMeaning

#print axioms PASoundness.PAtoCompactPairMeaning.pairFormula_semantics
#print axioms PASoundness.PAtoCompactPairMeaning.pairFormula_realize_iff
