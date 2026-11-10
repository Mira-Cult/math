import PASoundness.PAtoCompactCandidateInductionExact
import PASoundness.PAtoCompactCandidateNonemptyAlpha
import PASoundness.PAtoCompactZeroSuccessor

/-! Pointwise composition toward candidate-domain induction. A supplied
candidate successor, local base and local step assumptions yield the predicate
at its predecessor. No successor existence, global schemas, quotient or PA
proof translation is claimed here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateGlobalPoint
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateInductionExact
open PASoundness.PAtoCompactCandidateNonemptyAlpha PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactQuantifiedRefutation
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The successor graph supplies predecessor membership; alpha-renaming its
candidate's least nonempty binder supplies the exact local induction theorem.
All syntactic freshness conditions and local schemas remain explicit. -/
def candidate_global_point
    (x Y t u l v m r z w p q uD tD bD aD sD W : Nat) (f : CompactNamed.Formula)
    (freshNonempty : [Y,u,t,l,m,r,x].Nodup)
    (freshI : [Y,t,x,u,m,r].Nodup) (freshD : [m,p,q,uD,t,v,tD,w].Nodup)
    (freshOuter : [Y,m,p,q,bD,aD,t,v,tD,uD,sD].Nodup)
    (freshAlpha : [Y,u,t,m,r,aD,v,tD].Nodup)
    (hWx : W ≠ x) (hWY : W ≠ Y)
    (htf : t ∉ f.binders) (hxf : x ∉ f.binders)
    (hcOthers : filterPredicate Y t (neg f.encode) ∉ [x,u,m,r])
    (hcf : filterPredicate Y t (neg f.encode) ∉ f.names)
    (hYt : Y ≠ t) (htv : t ≠ v) (htm : t ≠ m) (hzm : z ≠ m)
    (hmf : m ∉ f.names) (hvf : v ∉ f.names)
    (hvY : v ≠ Y) (hvm : v ≠ m) (hvz : v ≠ z)
    (hvc : v ≠ filterPredicate Y t (neg f.encode))
    (hrc : r ≠ filterPredicate Y t (neg f.encode)) (hrm : r ≠ m) (hrv : r ≠ v)
    (hwv : w ≠ v) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpv : p ≠ v) (hpq : p ≠ q) (hqm : q ≠ m) (hqv : q ≠ v)
    (hpY : p ≠ Y) (hqY : q ≠ Y) (hmY : m ≠ Y) (hvp : v ≠ p) (hvq : v ≠ q)
    (hmGraph : m ∉ (namedFilterGraph Y t f).names)
    (hcBase : filterPredicate Y t (neg f.encode) ∉ (namedAllBase t m z f).names)
    (hcStep : filterPredicate Y t (neg f.encode) ∉ (namedAllSteps Y t v m w p q f).names)
    (hcClass : filterPredicate Y t (neg f.encode) ∉ (namedAllClassification Y v m z w p q).names) :
    let inst := (CompactNamed.replace t x f).encode
    let Wtn := both (successorCode x Y W) (candidateCode Y bD p q u t l m r)
    KDerivation (imp (uniformBaseCode t m z f) (imp (allStepsCode Y t v m w p q f)
      (imp Wtn inst))) := by
  dsimp only
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let B := uniformBaseCode t m z f
  let S := allStepsCode Y t v m w p q f
  let V := both (successorCode x Y W) (candidateCode Y bD p q u t l m r)
  let Γ := [V,S,B]
  have hv : Context Γ V := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hsucc : Context Γ (successorCode x Y W) := Context.conjunctionLeft hv
  have hcand : Context Γ (candidateCode Y bD p q u t l m r) := Context.conjunctionRight hv
  have hmem : Context Γ (member Y x) :=
    .mp hsucc (.closed (successor_contains_input x Y W hWx hWY))
  have hcand' : Context Γ (candidateCode Y bD p q u t x m r) :=
    .mp hcand (.closed (candidate_nonempty_rename Y bD p q u t l m r x freshNonempty))
  have hi := exact_candidate_induction_instance Y t x u v m r z w p q uD tD bD aD sD f
    freshI freshD freshOuter freshAlpha htf hxf hcOthers hcf hYt htv htm hzm hmf hvf
    hvY hvm hvz hvc hrc hrm hrv hwv hwm hpm hpv hpq hqm hqv hpY hqY hmY hvp hvq
    hmGraph hcBase hcStep hcClass
  exact .mp hmem (.mp hs (.mp hb (.mp hcand' (.closed hi))))

theorem candidate_global_point_certificate
    (x Y t u l v m r z w p q uD tD bD aD sD W : Nat) (f : CompactNamed.Formula)
    (freshNonempty : [Y,u,t,l,m,r,x].Nodup)
    (freshI : [Y,t,x,u,m,r].Nodup) (freshD : [m,p,q,uD,t,v,tD,w].Nodup)
    (freshOuter : [Y,m,p,q,bD,aD,t,v,tD,uD,sD].Nodup)
    (freshAlpha : [Y,u,t,m,r,aD,v,tD].Nodup)
    (hWx : W ≠ x) (hWY : W ≠ Y)
    (htf : t ∉ f.binders) (hxf : x ∉ f.binders)
    (hcOthers : filterPredicate Y t (neg f.encode) ∉ [x,u,m,r])
    (hcf : filterPredicate Y t (neg f.encode) ∉ f.names)
    (hYt : Y ≠ t) (htv : t ≠ v) (htm : t ≠ m) (hzm : z ≠ m)
    (hmf : m ∉ f.names) (hvf : v ∉ f.names)
    (hvY : v ≠ Y) (hvm : v ≠ m) (hvz : v ≠ z)
    (hvc : v ≠ filterPredicate Y t (neg f.encode))
    (hrc : r ≠ filterPredicate Y t (neg f.encode)) (hrm : r ≠ m) (hrv : r ≠ v)
    (hwv : w ≠ v) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpv : p ≠ v) (hpq : p ≠ q) (hqm : q ≠ m) (hqv : q ≠ v)
    (hpY : p ≠ Y) (hqY : q ≠ Y) (hmY : m ≠ Y) (hvp : v ≠ p) (hvq : v ≠ q)
    (hmGraph : m ∉ (namedFilterGraph Y t f).names)
    (hcBase : filterPredicate Y t (neg f.encode) ∉ (namedAllBase t m z f).names)
    (hcStep : filterPredicate Y t (neg f.encode) ∉ (namedAllSteps Y t v m w p q f).names)
    (hcClass : filterPredicate Y t (neg f.encode) ∉ (namedAllClassification Y v m z w p q).names) :
    let inst := (CompactNamed.replace t x f).encode
    let Wtn := both (successorCode x Y W) (candidateCode Y bD p q u t l m r)
    theoremCode (certificate (candidate_global_point x Y t u l v m r z w p q uD tD bD aD sD W f
    freshNonempty freshI freshD freshOuter freshAlpha hWx hWY htf hxf hcOthers hcf hYt htv htm hzm
    hmf hvf hvY hvm hvz hvc hrc hrm hrv hwv hwm hpm hpv hpq hqm hqv hpY hqY hmY hvp hvq
    hmGraph hcBase hcStep hcClass)) =
      imp (uniformBaseCode t m z f) (imp (allStepsCode Y t v m w p q f) (imp Wtn inst)) :=
  certificate_correct (candidate_global_point x Y t u l v m r z w p q uD tD bD aD sD W f
    freshNonempty freshI freshD freshOuter freshAlpha hWx hWY htf hxf hcOthers hcf hYt htv htm hzm
    hmf hvf hvY hvm hvz hvc hrc hrm hrv hwv hwm hpm hpv hpq hqm hqv hpY hqY hmY hvp hvq
    hmGraph hcBase hcStep hcClass)

end PASoundness.PAtoCompactCandidateGlobalPoint

#print axioms PASoundness.PAtoCompactCandidateGlobalPoint.candidate_global_point
#print axioms PASoundness.PAtoCompactCandidateGlobalPoint.candidate_global_point_certificate
