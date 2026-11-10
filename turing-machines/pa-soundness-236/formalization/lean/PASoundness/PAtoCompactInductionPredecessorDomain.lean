import PASoundness.PAtoCompactCandidateMemberClosure
import PASoundness.PAtoCompactCandidateDomainAlphaIndependent
import PASoundness.PAtoCompactUniformStep

/-! Candidate inheritance at a predecessor in the exact induction step core.
The candidate container Y is not required: the successor output z itself
contains the predecessor y. No formula-substitution compatibility is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInductionPredecessorDomain
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateMemberClosure
open PASoundness.PAtoCompactCandidateDomainAlphaIndependent PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation

/-- A candidate successor's predecessor has the allocator-indexed candidate
guard. All internal binder distinctness and the allocator bound are explicit. -/
def predecessor_domain_from_output
    (base Y y z w p q d u k c h g v r s : Nat)
    (hy : y < base + 32) (hwy : w ≠ y) (hwz : w ≠ z)
    (fresh : [z,y,d,p,q,v,u,k,c,h,g,r,s].Nodup) :
    KDerivation (imp (candidateCode z d p q u k c h g)
      (imp (predecessorCore Y y z w p q) (domainAt base y).encode)) := by
  have fy : [y,v,p,q,r,k,c,h,g].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  let C := candidateCode z d p q u k c h g
  let P := predecessorCore Y y z w p q
  let S := successorCode y z w
  let D := candidateCode y v p q r k c h g
  let Γ := [P,C]
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hs : Context Γ S := Context.conjunctionLeft (Context.conjunctionRight hp)
  have hm : Context Γ (member z y) := .mp hs (.closed (successor_contains_input y z w hwy hwz))
  have hd : Context Γ D := .mp hm (.mp hc (.closed (candidate_member z y d p q v u k c h g r s fresh)))
  have hdom : Context Γ (domainAt base y).encode :=
    .mp hd (.closed (candidate_to_domain y v p q r k c h g base fy hy))
  exact Context.closeEmpty (Context.deduction (Context.deduction hdom))

theorem predecessor_domain_from_output_certificate
    (base Y y z w p q d u k c h g v r s : Nat)
    (hy : y < base + 32) (hwy : w ≠ y) (hwz : w ≠ z)
    (fresh : [z,y,d,p,q,v,u,k,c,h,g,r,s].Nodup) :
    theoremCode (certificate (predecessor_domain_from_output base Y y z w p q d u k c h g v r s
      hy hwy hwz fresh)) =
      imp (candidateCode z d p q u k c h g)
        (imp (predecessorCore Y y z w p q) (domainAt base y).encode) := certificate_correct _
end PASoundness.PAtoCompactInductionPredecessorDomain

#print axioms PASoundness.PAtoCompactInductionPredecessorDomain.predecessor_domain_from_output
#print axioms PASoundness.PAtoCompactInductionPredecessorDomain.predecessor_domain_from_output_certificate
