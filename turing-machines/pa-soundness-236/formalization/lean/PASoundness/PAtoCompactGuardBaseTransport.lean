import PASoundness.PAtoCompactTermTranslation
import PASoundness.PAtoCompactCandidateBinderBridge

/-! Candidate-domain guard transport across fresh private binder blocks. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactGuardBaseTransport

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactCandidateFieldTransport PASoundness.PAtoCompactCandidateBinderBridge
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactGreatestSuccessor

theorem domainAt_encode (base x : Nat) :
    (domainAt base x).encode = candidateCode x (base+32) (base+33) (base+34)
      (base+35) (base+36) (base+37) (base+38) (base+39) := by
  simp [domainAt, mapNames, domainTemplate, oneMap, andF, namedTransitive,
    namedMembersTransitive, namedGreatestSubsetsBody, namedLeastSubsetsBody,
    namedLeastMember, namedGreatestBody, transitiveBody, namedBoth, namedEither,
    Formula.encode, Formula.not, candidateCode, oneLevelTransitiveCode,
    transitiveCode, membersTransitiveCode, greatestSubsetsCode, leastSubsetsCode,
    subsetCode, nonemptyCode, hasGreatestCode, greatestCode, leastMemberCode,
    CompactProof.both, CompactProof.neg,
    CompactDerivations.either, Nat.add_assoc]

macro "guard_fresh" : tactic => `(tactic|
  (simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true]; omega))

/-- Transport between disjoint private blocks, by explicit K alpha conversions. -/
def disjoint_candidate_transport (b c x : Nat) (hxb : x < b + 32)
    (hxc : x < c + 32) (hdis : b + 39 < c + 32 ∨ c + 39 < b + 32) :
    KDerivation (imp
      (candidateCode x (b+32) (b+33) (b+34) (b+35) (b+36) (b+37) (b+38) (b+39))
      (candidateCode x (c+32) (c+33) (c+34) (c+35) (c+36) (c+37) (c+38) (c+39))) := by
  have h1 := transitivity_field x (b+32) (b+33) (b+34) (b+35) (b+36) (b+37) (b+38) (b+39)
    (c+33) (c+34) (by guard_fresh)
  have h2 := member_field x (b+32) (c+33) (c+34) (b+35) (b+36) (b+37) (b+38) (b+39)
    (c+32) (by guard_fresh)
  have h3 := subset_field x (c+32) (c+33) (c+34) (b+35) (b+36) (b+37) (b+38) (b+39)
    (c+35) (by guard_fresh) (by guard_fresh)
  have h4 := subset_test_field x (c+32) (c+33) (c+34) (c+35) (b+36) (b+37) (b+38) (b+39)
    (c+36) (by guard_fresh) (by guard_fresh)
  have h5 := nonempty_field x (c+32) (c+33) (c+34) (c+35) (c+36) (b+37) (b+38) (b+39)
    (c+37) (by guard_fresh)
  have h6 := witness_field x (c+32) (c+33) (c+34) (c+35) (c+36) (c+37) (b+38) (b+39)
    (c+38) (by guard_fresh) (by guard_fresh)
  have h7 := order_field x (c+32) (c+33) (c+34) (c+35) (c+36) (c+37) (c+38) (b+39)
    (c+39) (by guard_fresh) (by guard_fresh)
  exact compose h1 (compose h2 (compose h3 (compose h4 (compose h5 (compose h6 h7)))))

/-- Transport a candidate guard between arbitrary private blocks above its
input name. A third block avoids capture even when the given blocks overlap. -/
def domainAt_transport (b c x : Nat) (hxb : x < b + 32) (hxc : x < c + 32) :
    KDerivation (imp (domainAt b x).encode (domainAt c x).encode) := by
  let d := max b c + 100
  have hbd : b + 39 < d + 32 := by dsimp [d]; omega
  have hcd : c + 39 < d + 32 := by dsimp [d]; omega
  have hxd : x < d + 32 := by omega
  rw [domainAt_encode, domainAt_encode]
  exact compose (disjoint_candidate_transport b d x hxb hxd (Or.inl hbd))
    (disjoint_candidate_transport d c x hxd hxc (Or.inr hcd))

theorem domainAt_transport_certificate (b c x : Nat)
    (hxb : x < b + 32) (hxc : x < c + 32) :
    theoremCode (certificate (domainAt_transport b c x hxb hxc)) =
      imp (domainAt b x).encode (domainAt c x).encode :=
  certificate_correct (domainAt_transport b c x hxb hxc)

end PASoundness.PAtoCompactGuardBaseTransport

#print axioms PASoundness.PAtoCompactGuardBaseTransport.domainAt_encode
#print axioms PASoundness.PAtoCompactGuardBaseTransport.disjoint_candidate_transport
#print axioms PASoundness.PAtoCompactGuardBaseTransport.domainAt_transport
#print axioms PASoundness.PAtoCompactGuardBaseTransport.domainAt_transport_certificate
