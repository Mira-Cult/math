import PASoundness.PAtoCompactOuterDomain

/-! Candidate-relative induction instance: the prior all-members-domain
premise is derived from explicit one-level transitivity and greatest-subset
conditions. Base, step, least-subsets and membership remain explicit K
antecedents; no candidate existence, unrestricted induction, quotient or PA
interpretation is asserted. Code 1 is literal self-membership. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateInduction
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactOuterDomain PASoundness.PAtoCompactDomainClassification
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactUniformBase PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactQuantifiedRefutation PASoundness.PAtoCompactLeastCounterexample
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A named induction instance under explicit outer candidate conditions and
base/step hypotheses. The extra numeric freshness assumptions protect the
literal compact binders and generated filter witness. -/
def candidate_induction_instance
    (x t a u y m r z w p q uD kD tD bD aD sD : Nat) (f : CompactNamed.Formula)
    (freshI : [x,t,a,u,m,r].Nodup) (freshD : [m,p,q,uD,kD,y,tD,w].Nodup)
    (freshOuter : [x,m,p,q,bD,aD,kD,y,tD,uD,sD].Nodup)
    (htf : t ∉ f.binders) (haf : a ∉ f.binders)
    (hcOthers : filterPredicate x t (neg f.encode) ∉ [a,u,m,r])
    (hcf : filterPredicate x t (neg f.encode) ∉ f.names)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m) (hzm : z ≠ m)
    (hmf : m ∉ f.names) (hyf : y ∉ f.names)
    (hyx : y ≠ x) (hym : y ≠ m) (hyz : y ≠ z)
    (hyc : y ≠ filterPredicate x t (neg f.encode))
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y)
    (hpx : p ≠ x) (hqx : q ≠ x) (hmx : m ≠ x) (hyp : y ≠ p) (hyq : y ≠ q)
    (hmGraph : m ∉ (namedFilterGraph x t f).names)
    (hcBase : filterPredicate x t (neg f.encode) ∉ (namedAllBase t m z f).names)
    (hcStep : filterPredicate x t (neg f.encode) ∉ (namedAllSteps x t y m w p q f).names)
    (hcClass : filterPredicate x t (neg f.encode) ∉ (namedAllClassification x y m z w p q).names) :
    let inst := (CompactNamed.replace t a f).encode
    KDerivation (imp (oneLevelTransitiveCode x bD p q)
      (imp (greatestSubsetsCode x aD kD y tD)
        (imp (uniformBaseCode t m z f) (imp (allStepsCode x t y m w p q f)
          (imp (leastSubsetsCode x u t a m r) (imp (member x a) inst)))))) := by
  dsimp only
  let D := oneLevelTransitiveCode x bD p q
  let G := greatestSubsetsCode x aD kD y tD
  let Γ := [G,D]
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hm : Context Γ (allMembersDomainCode x m p q uD kD y tD) :=
    .mp hg (.mp hd (.closed (all_members_domain x m p q bD aD kD y tD uD sD freshOuter)))
  have hi := domain_conditioned_induction_instance x t a u y m r z w p q uD kD tD f
    freshI freshD htf haf hcOthers hcf hxt hty htm hzm hmf hyf hyx hym hyz hyc hrc hrm hry
    hwy hwm hpm hpy hpq hqm hqy hpx hqx hmx hyp hyq hmGraph hcBase hcStep hcClass
  have hc := Context.mp hm (.mp (Context.conjunctionLeft hd) (.closed hi))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hc

theorem candidate_induction_certificate
    (x t a u y m r z w p q uD kD tD bD aD sD : Nat) (f : CompactNamed.Formula)
    (freshI : [x,t,a,u,m,r].Nodup) (freshD : [m,p,q,uD,kD,y,tD,w].Nodup)
    (freshOuter : [x,m,p,q,bD,aD,kD,y,tD,uD,sD].Nodup)
    (htf : t ∉ f.binders) (haf : a ∉ f.binders)
    (hcOthers : filterPredicate x t (neg f.encode) ∉ [a,u,m,r])
    (hcf : filterPredicate x t (neg f.encode) ∉ f.names)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m) (hzm : z ≠ m)
    (hmf : m ∉ f.names) (hyf : y ∉ f.names)
    (hyx : y ≠ x) (hym : y ≠ m) (hyz : y ≠ z)
    (hyc : y ≠ filterPredicate x t (neg f.encode))
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y)
    (hpx : p ≠ x) (hqx : q ≠ x) (hmx : m ≠ x) (hyp : y ≠ p) (hyq : y ≠ q)
    (hmGraph : m ∉ (namedFilterGraph x t f).names)
    (hcBase : filterPredicate x t (neg f.encode) ∉ (namedAllBase t m z f).names)
    (hcStep : filterPredicate x t (neg f.encode) ∉ (namedAllSteps x t y m w p q f).names)
    (hcClass : filterPredicate x t (neg f.encode) ∉ (namedAllClassification x y m z w p q).names) :
    let inst := (CompactNamed.replace t a f).encode
    theoremCode (certificate (candidate_induction_instance x t a u y m r z w p q uD kD tD bD aD sD f
      freshI freshD freshOuter htf haf hcOthers hcf hxt hty htm hzm hmf hyf hyx hym hyz hyc
      hrc hrm hry hwy hwm hpm hpy hpq hqm hqy hpx hqx hmx hyp hyq hmGraph hcBase hcStep hcClass)) =
      imp (oneLevelTransitiveCode x bD p q)
        (imp (greatestSubsetsCode x aD kD y tD)
          (imp (uniformBaseCode t m z f) (imp (allStepsCode x t y m w p q f)
            (imp (leastSubsetsCode x u t a m r) (imp (member x a) inst))))) :=
  certificate_correct (candidate_induction_instance x t a u y m r z w p q uD kD tD bD aD sD f
    freshI freshD freshOuter htf haf hcOthers hcf hxt hty htm hzm hmf hyf hyx hym hyz hyc
    hrc hrm hry hwy hwm hpm hpy hpq hqm hqy hpx hqx hmx hyp hyq hmGraph hcBase hcStep hcClass)

end PASoundness.PAtoCompactCandidateInduction

#print axioms PASoundness.PAtoCompactCandidateInduction.candidate_induction_instance
#print axioms PASoundness.PAtoCompactCandidateInduction.candidate_induction_certificate
