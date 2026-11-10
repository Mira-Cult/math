import PASoundness.PAtoCompactCandidateExact
import PASoundness.PAtoCompactPredecessorDomain
import PASoundness.PAtoCompactOuterDomain
import PASoundness.PAtoCompactLeastDownward

/-! A member of a candidate is a candidate, using finite K proof data and
explicit pairwise-fresh names. No standard-model soundness is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateMemberClosure
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactPredecessorDomain
open PASoundness.PAtoCompactOuterDomain PASoundness.PAtoCompactGreatestDownward
open PASoundness.PAtoCompactLeastDownward PASoundness.PAtoCompactLeastCounterexample
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Each member of a candidate satisfies the same candidate condition, with
new member and subset binders v and r. All labels are pairwise fresh. -/
def candidate_member (x y b p q v a k l m g r s : Nat)
    (fresh : [x,y,b,p,q,v,a,k,l,m,g,r,s].Nodup) :
    KDerivation (imp (candidateCode x b p q a k l m g) (imp (member x y)
      (candidateCode y v p q r k l m g))) := by
  have hf1 : [x,y,b,p,q,v].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  have hf2 : [x,y,p,q,k].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  have hf3 : [x,y,a,k,m,g,r,s].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  have hf4 : [x,y,a,k,l,m,g,r,s].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  let D := candidateCode x b p q a k l m g
  let X := member x y
  let Γ := [X,D]
  have hx : Context Γ X := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have ht : Context Γ (oneLevelTransitiveCode x b p q) := Context.conjunctionLeft hd
  have hr := Context.conjunctionRight hd
  have hg : Context Γ (greatestSubsetsCode x a k m g) := Context.conjunctionLeft hr
  have hl : Context Γ (leastSubsetsCode x a k l m g) := Context.conjunctionRight hr
  have hy : Context Γ (oneLevelTransitiveCode y v p q) :=
    .mp hx (.mp ht (.closed (member_one_level_transitive x y b p q v hf1)))
  have hs : Context Γ (subsetCode y x k) :=
    .mp hx (.mp (Context.conjunctionLeft ht) (.closed (transitive_member_subset x y p q k hf2)))
  have hg' : Context Γ (greatestSubsetsCode y r k m g) :=
    .mp hs (.mp hg (.closed (greatest_subsets_downward x y a k m g r s hf3)))
  have hl' : Context Γ (leastSubsetsCode y r k l m g) :=
    .mp hs (.mp hl (.closed (least_subsets_downward x y a k l m g r s hf4)))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact Context.conjunctionIntro hy (Context.conjunctionIntro hg' hl')

theorem candidate_member_certificate (x y b p q v a k l m g r s : Nat)
    (fresh : [x,y,b,p,q,v,a,k,l,m,g,r,s].Nodup) :
    theoremCode (certificate (candidate_member x y b p q v a k l m g r s fresh)) =
      imp (candidateCode x b p q a k l m g) (imp (member x y)
        (candidateCode y v p q r k l m g)) :=
  certificate_correct (candidate_member x y b p q v a k l m g r s fresh)

end PASoundness.PAtoCompactCandidateMemberClosure

#print axioms PASoundness.PAtoCompactCandidateMemberClosure.candidate_member
#print axioms PASoundness.PAtoCompactCandidateMemberClosure.candidate_member_certificate
