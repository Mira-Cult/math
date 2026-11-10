import PASoundness.PAtoCompactTransitiveSemantics
import PASoundness.PAtoCompactTransitiveOrdinal
import PASoundness.PAtoCompactOrdinalExtrema

/-! Exact standard-HF extension of the explicit candidate ordinal domain.
This is semantic truth calibration and does not prove an internal K quotient,
induction, arithmetic operations or a PA proof translation. -/
namespace PASoundness.PAtoCompactCandidateStandard
open PASoundness.CompactMatrix PASoundness.CompactSemantics PASoundness.CompactProof
open PASoundness.HFCoding PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactTransitiveSemantics PASoundness.PAtoCompactTransitiveOrdinal
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactOrdinalExtrema

/-- The exact proposed transitivity/extrema domain code has precisely the
finite ordinal codes as values in standard HF, with all labels fresh. -/
theorem candidate_standard_iff (x b p q u k a m r : Nat) (ρ : Environment)
    (fresh : [x,b,p,q,u,k,a,m,r].Nodup) :
    (decode (both (oneLevelTransitiveCode x b p q)
      (both (greatestSubsetsCode x u k m r) (leastSubsetsCode x u k a m r)))).Realize ρ ↔
      ∃ n, ρ x = (ordinal n).code := by
  have f4 : [x,b,p,q].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, not_false_eq_true] at fresh ⊢
    tauto
  have f6 : [x,u,k,a,m,r].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, not_false_eq_true] at fresh ⊢
    tauto
  rw [realize_both, realize_both]
  constructor
  · rintro ⟨ht,_⟩
    have h := (one_level_meaning x b p q ρ f4).mp ht
    have htrans : ∀ v : Object, v ∈ (⟨ρ x⟩ : Object) →
        ∀ w : Object, w ∈ v → w ∈ (⟨ρ x⟩ : Object) := by
      rintro ⟨v⟩ hv ⟨w⟩ hw
      exact h.1 v w hv hw
    have hmembers : ∀ v : Object, v ∈ (⟨ρ x⟩ : Object) →
        ∀ w : Object, w ∈ v → ∀ z : Object, z ∈ w → z ∈ v := by
      rintro ⟨v⟩ hv ⟨w⟩ hw ⟨z⟩ hz
      exact h.2 v hv w z hw hz
    obtain ⟨n,hn⟩ := transitive_members_ordinal ⟨ρ x⟩ htrans hmembers
    exact ⟨n, congrArg Object.code hn⟩
  · rintro ⟨n,hn⟩
    have hxb : x ≠ b := by intro he; subst x; simp at f4
    have hxp : x ≠ p := by intro he; subst x; simp at f4
    have hxq : x ≠ q := by intro he; subst x; simp at f4
    have hbp : b ≠ p := by intro he; subst b; simp at f4
    have hbq : b ≠ q := by intro he; subst b; simp at f4
    have hpq : p ≠ q := by intro he; subst p; simp at f4
    have ht := ordinal_one_level_transitive x b p q n ρ hxb hxp hxq hbp hbq hpq hn
    have he := ordinal_extrema_codes x u k a m r n ρ f6 hn
    exact ⟨ht,he.2,he.1⟩

end PASoundness.PAtoCompactCandidateStandard

#print axioms PASoundness.PAtoCompactCandidateStandard.candidate_standard_iff
