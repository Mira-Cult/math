import PASoundness.PAtoCompactCandidateMemberClosure
import PASoundness.PAtoCompactUniformStep

/-! Candidate endpoints of the exact predecessor core used by the global
induction engine. This is finite K proof data; it does not translate a PA
formula or prove an induction axiom. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidatePredecessorCore
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateMemberClosure
open PASoundness.PAtoCompactUniformStep PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- From a candidate container and the named predecessor core, both its
member y and the explicitly represented successor z are candidates. The two
freshness lists are separate, and the transitivity conjunct of the core is not
needed for this proof. -/
def predecessor_core_candidates
    (Y y z w b p q v a k l h g r s d e i u j n c o : Nat)
    (freshMember : [Y,y,b,p,q,v,a,k,l,h,g,r,s].Nodup)
    (freshSucc : [y,z,w,v,p,q,d,e,i,r,k,h,g,u,l,j,n,c,o].Nodup) :
    KDerivation (imp (candidateCode Y b p q a k l h g)
      (imp (predecessorCore Y y z w p q)
        (both (candidateCode y v p q r k l h g)
          (candidateCode z d p q u k c h g)))) := by
  let D := candidateCode Y b p q a k l h g
  let P := predecessorCore Y y z w p q
  let Γ := [P,D]
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hy : Context Γ (member Y y) := Context.conjunctionLeft hp
  have hs : Context Γ (successorCode y z w) := Context.conjunctionLeft (Context.conjunctionRight hp)
  have hcy : Context Γ (candidateCode y v p q r k l h g) :=
    .mp hy (.mp hd (.closed (candidate_member Y y b p q v a k l h g r s freshMember)))
  have hcz : Context Γ (candidateCode z d p q u k c h g) :=
    .mp hs (.mp hcy (.closed (candidate_exact_successor y z w v p q d e i r k h g u l j n c o freshSucc)))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact Context.conjunctionIntro hcy hcz

theorem predecessor_core_candidates_certificate
    (Y y z w b p q v a k l h g r s d e i u j n c o : Nat)
    (freshMember : [Y,y,b,p,q,v,a,k,l,h,g,r,s].Nodup)
    (freshSucc : [y,z,w,v,p,q,d,e,i,r,k,h,g,u,l,j,n,c,o].Nodup) :
    theoremCode (certificate (predecessor_core_candidates Y y z w b p q v a k l h g r s d e i u j n c o freshMember freshSucc)) =
      imp (candidateCode Y b p q a k l h g)
        (imp (predecessorCore Y y z w p q)
          (both (candidateCode y v p q r k l h g)
            (candidateCode z d p q u k c h g))) :=
  certificate_correct (predecessor_core_candidates Y y z w b p q v a k l h g r s d e i u j n c o freshMember freshSucc)

end PASoundness.PAtoCompactCandidatePredecessorCore

#print axioms PASoundness.PAtoCompactCandidatePredecessorCore.predecessor_core_candidates
#print axioms PASoundness.PAtoCompactCandidatePredecessorCore.predecessor_core_candidates_certificate
