import PASoundness.Peano
import PASoundness.PAtoCompactCandidateQuantifiers

/-! A single structural truth-preservation step for a proposed PA-to-compact
interpretation. The body translation is a parameter, and its truth theorem is
an explicit hypothesis. No PA-to-K proof translation or arithmetic axiom
certificates are constructed here. -/
namespace PASoundness.PAtoCompactRelativizedTruth

open PASoundness.CompactMatrix PASoundness.CompactSemantics PASoundness.CompactProof
open PASoundness.HFCoding PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactCandidateQuantifiers
open FirstOrder FirstOrder.Language

/-- Represent each arithmetic assignment value by its finite ordinal HF code. -/
def ordinalAssignment (v : Nat → Nat) : Environment := fun x => (ordinal (v x)).code

/-- The literal candidate domain used by the guarded quantifier. -/
def candidate (x b p q u k a m r : Nat) : Nat :=
  both (oneLevelTransitiveCode x b p q)
    (both (greatestSubsetsCode x u k m r) (leastSubsetsCode x u k a m r))

/-- Updating a coded assignment agrees exactly with coding the updated
arithmetic assignment. -/
theorem ordinalAssignment_update (v : Nat → Nat) (x n : Nat) :
    update (ordinalAssignment v) x (ordinal n).code =
      ordinalAssignment (Function.update v x n) := by
  funext y
  by_cases h : y = x
  · subst y
    simp [update, ordinalAssignment]
  · simp [update, ordinalAssignment, h]

/-- If a compact body has the stated truth behavior for *every* arithmetic
assignment, then the literal candidate-guarded compact universal has the truth
behavior of PA's capture-avoiding named universal. The freshness list concerns
the candidate's internal syntactic labels; the body code is not substituted or
renamed, and must already use the given assignment convention. -/
theorem guarded_all_truth (x b p q u k a m r body : Nat)
    (φ : PASoundness.Peano.Formula)
    (fresh : [x,b,p,q,u,k,a,m,r].Nodup)
    (body_truth : ∀ v : Nat → Nat,
      (decode body).Realize (ordinalAssignment v) ↔ φ.Realize v)
    (v : Nat → Nat) :
    (decode (allCode x (imp (candidate x b p q u k a m r) body))).Realize
      (ordinalAssignment v) ↔ (PASoundness.FOL.allAt x φ).Realize v := by
  rw [realize_all]
  simp only [realize_imp, candidate]
  rw [candidate_forall x b p q u k a m r (ordinalAssignment v) fresh
    (fun z => (decode body).Realize (update (ordinalAssignment v) x z))]
  rw [PASoundness.FOL.realize_allAt]
  apply forall_congr'
  intro n
  rw [ordinalAssignment_update]
  exact body_truth _

end PASoundness.PAtoCompactRelativizedTruth

#print axioms PASoundness.PAtoCompactRelativizedTruth.guarded_all_truth
