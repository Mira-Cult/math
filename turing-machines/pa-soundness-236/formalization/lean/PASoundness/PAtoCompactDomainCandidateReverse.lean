import PASoundness.PAtoCompactGuardBaseTransport

/-! Reverse alpha transport from an allocated domain guard to an arbitrary
candidate with pairwise distinct names. Finite K proof data only; no semantic
soundness or induction schema is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDomainCandidateReverse
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactCandidateFieldTransport PASoundness.PAtoCompactCandidateBinderBridge
open PASoundness.PAtoCompactGuardBaseTransport
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- An allocated candidate domain entails the same candidate with any pairwise
distinct internal names. An intermediate disjoint block permits the requested
names to overlap the original allocator block. -/
def domain_to_candidate (x b p q a k l m g c : Nat)
    (fresh : [x,b,p,q,a,k,l,m,g].Nodup) (hxc : x < c+32) :
    KDerivation (imp (domainAt c x).encode (candidateCode x b p q a k l m g)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at fresh
  let d := x+b+p+q+a+k+l+m+g+100
  have hxd : x < d+32 := by dsimp only [d]; omega
  have h7 := order_field x (d+32) (d+33) (d+34) (d+35) (d+36) (d+37) (d+38) (d+39) g (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto) (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto)
  have h6 := witness_field x (d+32) (d+33) (d+34) (d+35) (d+36) (d+37) (d+38) g m (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto) (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto)
  have h5 := nonempty_field x (d+32) (d+33) (d+34) (d+35) (d+36) (d+37) m g l (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto)
  have h4 := subset_test_field x (d+32) (d+33) (d+34) (d+35) (d+36) l m g k (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto) (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto)
  have h3 := subset_field x (d+32) (d+33) (d+34) (d+35) k l m g a (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto) (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto)
  have h2 := member_field x (d+32) (d+33) (d+34) a k l m g b (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto)
  have h1 := transitivity_field x b (d+33) (d+34) a k l m g p q (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto)
  have hout : KDerivation (imp (domainAt d x).encode (candidateCode x b p q a k l m g)) := by
    rw [domainAt_encode]
    exact compose h7 (compose h6 (compose h5 (compose h4 (compose h3 (compose h2 h1)))))
  exact compose (domainAt_transport c d x hxc hxd) hout

theorem domain_to_candidate_certificate (x b p q a k l m g c : Nat)
    (fresh : [x,b,p,q,a,k,l,m,g].Nodup) (hxc : x < c+32) :
    theoremCode (certificate (domain_to_candidate x b p q a k l m g c fresh hxc)) =
      imp (domainAt c x).encode (candidateCode x b p q a k l m g) :=
  certificate_correct _
end PASoundness.PAtoCompactDomainCandidateReverse

#print axioms PASoundness.PAtoCompactDomainCandidateReverse.domain_to_candidate
#print axioms PASoundness.PAtoCompactDomainCandidateReverse.domain_to_candidate_certificate
