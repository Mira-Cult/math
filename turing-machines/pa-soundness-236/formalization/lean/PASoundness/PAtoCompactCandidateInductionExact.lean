import PASoundness.PAtoCompactCandidateInduction
import PASoundness.PAtoCompactCandidateExact
import PASoundness.PAtoCompactCandidateAlphaOuter
import PASoundness.PAtoCompactGreatestWitnessAlpha
import PASoundness.PAtoCompactGreatestInnerAlpha

/-! A candidateCode-relative K induction instance. Capture-safe alpha
conversions align the candidate's shared greatest/least binders with the
induction theorem's fresh names. Base, step and membership remain explicit
antecedents. This is not a complete PA interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateInductionExact
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactUniformStep PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactCandidateInduction PASoundness.PAtoCompactCandidateAlphaOuter
open PASoundness.PAtoCompactGreatestWitnessAlpha PASoundness.PAtoCompactGreatestInnerAlpha
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The literal candidate's greatest condition, capture-safely renamed to
separate its witnesses from the induction member name. -/
def candidate_greatest_renamed (x b p q u t a m r aD y tD : Nat)
    (fresh : [x,u,t,m,r,aD,y,tD].Nodup) :
    KDerivation (imp (candidateCode x b p q u t a m r)
      (greatestSubsetsCode x aD t y tD)) := by
  have h1 : [x,u,t,m,r,aD].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  have h2 : [x,aD,t,m,r,y].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  have h3 : [x,aD,t,y,r,tD].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  apply Context.closeEmpty
  apply Context.deduction
  have hd : Context [candidateCode x b p q u t a m r]
      (candidateCode x b p q u t a m r) := Context.head [] _
  have hg0 : Context [candidateCode x b p q u t a m r] (greatestSubsetsCode x u t m r) :=
    Context.conjunctionLeft (Context.conjunctionRight hd)
  have hg1 := Context.mp hg0 (.closed (greatest_subsets_rename_outer x u t m r aD h1))
  have hg2 := Context.mp hg1 (.closed (greatest_witness_rename x aD t m r y h2))
  exact .mp hg2 (.closed (greatest_subsets_rename_order x aD t y r tD h3))

/-- A single predicate instance follows from the exact candidate, supplied
base and step schemata, and membership in the candidate. All explicit naming
hypotheses are retained; no arithmetic proof translation is claimed. -/
def exact_candidate_induction_instance
    (x t a u y m r z w p q uD tD bD aD sD : Nat) (f : CompactNamed.Formula)
    (freshI : [x,t,a,u,m,r].Nodup) (freshD : [m,p,q,uD,t,y,tD,w].Nodup)
    (freshOuter : [x,m,p,q,bD,aD,t,y,tD,uD,sD].Nodup)
    (freshAlpha : [x,u,t,m,r,aD,y,tD].Nodup)
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
    KDerivation (imp (candidateCode x bD p q u t a m r)
      (imp (uniformBaseCode t m z f) (imp (allStepsCode x t y m w p q f)
        (imp (member x a) inst)))) := by
  dsimp only
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let D := candidateCode x bD p q u t a m r
  let B := uniformBaseCode t m z f
  let S := allStepsCode x t y m w p q f
  let Γ := [member x a,S,B,D]
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have ha : Context Γ (member x a) := .hypothesis (by simp [Γ])
  have ht : Context Γ (oneLevelTransitiveCode x bD p q) := Context.conjunctionLeft hd
  have hl : Context Γ (leastSubsetsCode x u t a m r) :=
    Context.conjunctionRight (Context.conjunctionRight hd)
  have hg : Context Γ (greatestSubsetsCode x aD t y tD) :=
    .mp hd (.closed (candidate_greatest_renamed x bD p q u t a m r aD y tD freshAlpha))
  have hi := candidate_induction_instance x t a u y m r z w p q uD t tD bD aD sD f
    freshI freshD freshOuter htf haf hcOthers hcf hxt hty htm hzm hmf hyf hyx hym hyz hyc
    hrc hrm hry hwy hwm hpm hpy hpq hqm hqy hpx hqx hmx hyp hyq hmGraph hcBase hcStep hcClass
  exact .mp ha (.mp hl (.mp hs (.mp hb (.mp hg (.mp ht (.closed hi))))))

theorem exact_candidate_induction_certificate
    (x t a u y m r z w p q uD tD bD aD sD : Nat) (f : CompactNamed.Formula)
    (freshI : [x,t,a,u,m,r].Nodup) (freshD : [m,p,q,uD,t,y,tD,w].Nodup)
    (freshOuter : [x,m,p,q,bD,aD,t,y,tD,uD,sD].Nodup)
    (freshAlpha : [x,u,t,m,r,aD,y,tD].Nodup)
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
    theoremCode (certificate (exact_candidate_induction_instance x t a u y m r z w p q uD tD bD aD sD f
      freshI freshD freshOuter freshAlpha htf haf hcOthers hcf hxt hty htm hzm hmf hyf hyx hym hyz hyc
      hrc hrm hry hwy hwm hpm hpy hpq hqm hqy hpx hqx hmx hyp hyq hmGraph hcBase hcStep hcClass)) =
      imp (candidateCode x bD p q u t a m r)
        (imp (uniformBaseCode t m z f) (imp (allStepsCode x t y m w p q f)
          (imp (member x a) inst))) :=
  certificate_correct (exact_candidate_induction_instance x t a u y m r z w p q uD tD bD aD sD f
    freshI freshD freshOuter freshAlpha htf haf hcOthers hcf hxt hty htm hzm hmf hyf hyx hym hyz hyc
    hrc hrm hry hwy hwm hpm hpy hpq hqm hqy hpx hqx hmx hyp hyq hmGraph hcBase hcStep hcClass)

end PASoundness.PAtoCompactCandidateInductionExact

#print axioms PASoundness.PAtoCompactCandidateInductionExact.candidate_greatest_renamed
#print axioms PASoundness.PAtoCompactCandidateInductionExact.exact_candidate_induction_instance
#print axioms PASoundness.PAtoCompactCandidateInductionExact.exact_candidate_induction_certificate
