import PASoundness.PAtoCompactCandidateStandard

/-! Standard-HF quantifier calibration for the literal candidate ordinal
predicate. These are semantic interfaces for a future structural truth proof,
not a K derivation or completed PA interpretation. -/
namespace PASoundness.PAtoCompactCandidateQuantifiers
open PASoundness.CompactMatrix PASoundness.CompactSemantics PASoundness.CompactProof
open PASoundness.HFCoding PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactCandidateStandard

/-- A standard-HF universal quantifier guarded by the exact candidate
predicate ranges precisely over the finite ordinal codes. -/
theorem candidate_forall (x b p q u k a m r : Nat) (ρ : Environment)
    (fresh : [x,b,p,q,u,k,a,m,r].Nodup) (P : Nat → Prop) :
    (∀ v, (decode (both (oneLevelTransitiveCode x b p q)
      (both (greatestSubsetsCode x u k m r) (leastSubsetsCode x u k a m r)))).Realize
        (update ρ x v) → P v) ↔ ∀ n, P (ordinal n).code := by
  constructor
  · intro h n
    apply h
    apply (candidate_standard_iff x b p q u k a m r (update ρ x (ordinal n).code) fresh).mpr
    exact ⟨n, update_same ρ x _⟩
  · intro h v hv
    obtain ⟨n,hn⟩ := (candidate_standard_iff x b p q u k a m r (update ρ x v) fresh).mp hv
    rw [update_same] at hn
    simpa only [hn] using h n

/-- The corresponding existential guard ranges over the same codes. -/
theorem candidate_exists (x b p q u k a m r : Nat) (ρ : Environment)
    (fresh : [x,b,p,q,u,k,a,m,r].Nodup) (P : Nat → Prop) :
    (∃ v, (decode (both (oneLevelTransitiveCode x b p q)
      (both (greatestSubsetsCode x u k m r) (leastSubsetsCode x u k a m r)))).Realize
        (update ρ x v) ∧ P v) ↔ ∃ n, P (ordinal n).code := by
  constructor
  · rintro ⟨v,hv,hp⟩
    obtain ⟨n,hn⟩ := (candidate_standard_iff x b p q u k a m r (update ρ x v) fresh).mp hv
    rw [update_same] at hn
    exact ⟨n, hn ▸ hp⟩
  · rintro ⟨n,hp⟩
    refine ⟨(ordinal n).code, ?_, hp⟩
    apply (candidate_standard_iff x b p q u k a m r (update ρ x (ordinal n).code) fresh).mpr
    exact ⟨n, update_same ρ x _⟩

end PASoundness.PAtoCompactCandidateQuantifiers

#print axioms PASoundness.PAtoCompactCandidateQuantifiers.candidate_forall
#print axioms PASoundness.PAtoCompactCandidateQuantifiers.candidate_exists
