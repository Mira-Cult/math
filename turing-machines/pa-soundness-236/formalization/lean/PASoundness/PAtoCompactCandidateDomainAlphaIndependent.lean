import PASoundness.PAtoCompactGuardBaseTransport

/-! Finite K alpha-transport from a candidate with arbitrary distinct internal
names to an allocator-indexed domain guard. No semantic soundness is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateDomainAlphaIndependent
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactCandidateFieldTransport PASoundness.PAtoCompactCandidateBinderBridge
open PASoundness.PAtoCompactGuardBaseTransport

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A candidate with pairwise distinct object and binder names entails the
same candidate in any target domain allocation whose private block is above
the object name. A disjoint intermediate block handles arbitrary overlap. -/
def candidate_to_domain (x b p q a k l m g c : Nat)
    (fresh : [x,b,p,q,a,k,l,m,g].Nodup) (hxc : x < c + 32) :
    KDerivation (imp (candidateCode x b p q a k l m g) (domainAt c x).encode) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    not_or, List.nodup_nil, and_true] at fresh
  let d := x+b+p+q+a+k+l+m+g+100
  have hxd : x < d + 32 := by dsimp only [d]; omega
  have h1 := transitivity_field x b p q a k l m g (d+33) (d+34) (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto)
  have h2 := member_field x b (d+33) (d+34) a k l m g (d+32) (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto)
  have h3 := subset_field x (d+32) (d+33) (d+34) a k l m g (d+35) (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto) (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto)
  have h4 := subset_test_field x (d+32) (d+33) (d+34) (d+35) k l m g (d+36) (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto) (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto)
  have h5 := nonempty_field x (d+32) (d+33) (d+34) (d+35) (d+36) l m g (d+37) (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto)
  have h6 := witness_field x (d+32) (d+33) (d+34) (d+35) (d+36) (d+37) m g (d+38) (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto) (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto)
  have h7 := order_field x (d+32) (d+33) (d+34) (d+35) (d+36) (d+37) (d+38) g (d+39) (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto) (by
    dsimp only [d]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (clear fresh; omega) | tauto)
  have hin : KDerivation (imp (candidateCode x b p q a k l m g) (domainAt d x).encode) := by
    rw [domainAt_encode]
    exact compose h1 (compose h2 (compose h3 (compose h4 (compose h5 (compose h6 h7)))))
  exact compose hin (domainAt_transport d c x hxd hxc)

theorem candidate_to_domain_certificate (x b p q a k l m g c : Nat)
    (fresh : [x,b,p,q,a,k,l,m,g].Nodup) (hxc : x < c + 32) :
    theoremCode (certificate (candidate_to_domain x b p q a k l m g c fresh hxc)) =
      imp (candidateCode x b p q a k l m g) (domainAt c x).encode :=
  certificate_correct _
end PASoundness.PAtoCompactCandidateDomainAlphaIndependent

#print axioms PASoundness.PAtoCompactCandidateDomainAlphaIndependent.candidate_to_domain
#print axioms PASoundness.PAtoCompactCandidateDomainAlphaIndependent.candidate_to_domain_certificate
