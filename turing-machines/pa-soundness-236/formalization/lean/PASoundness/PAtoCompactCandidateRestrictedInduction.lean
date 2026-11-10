import PASoundness.PAtoCompactCandidateRestrictedCompose
import PASoundness.PAtoCompactCandidateGlobalPoint
import PASoundness.PAtoCompactCandidateFixed

/-! Conditional candidate-domain induction from a supplied global base
and a step schema restricted to candidate containers. The constructed successor is itself a candidate, so the step schema
need only apply to candidate containers. Explicit syntax-freshness and selector
guards remain; this does not establish PA induction translation or quotient equality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateRestrictedInduction
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateFixed
open PASoundness.PAtoCompactCandidateGlobalPoint PASoundness.PAtoCompactCandidateRestrictedCompose
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactQuantifiedRefutation
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- For a named predicate, K derives the value at a candidate element from the
supplied base schema and the step schema quantified over candidate containers.
All naming and selector conditions are explicit. -/
def candidate_restricted_induction
    (x Y t u l v m r z w p q uD tD bD aD sD W d s T U R Z V J point : Nat)
    (f : CompactNamed.Formula)
    (freshSucc : [x,Y,W,bD,p,q,d,s,T,u,t,m,r,U,l,R,Z,V,J,point].Nodup)
    (hWc : W ≠ adjunctionPredicate x point) (hYc : Y ≠ adjunctionPredicate x point)
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
    (hcClass : filterPredicate Y t (neg f.encode) ∉ (namedAllClassification Y v m z w p q).names)
    (hYBase : Y ∉ (namedAllBase t m z f).names)
    (hYInst : Y ∉ (CompactNamed.replace t x f).names) :
    let inst := (CompactNamed.replace t x f).encode
    let step := allCode Y (imp (candidateCode Y bD p q u t l m r)
      (allStepsCode Y t v m w p q f))
    KDerivation (imp (candidateCode x bD p q u t l m r)
      (imp (uniformBaseCode t m z f) (imp step inst))) := by
  dsimp only
  let D := candidateCode x bD p q u t l m r
  let B := uniformBaseCode t m z f
  let L := allStepsCode Y t v m w p q f
  let C := candidateCode Y bD p q u t l m r
  let S := allCode Y (imp C L)
  let F := (CompactNamed.replace t x f).encode
  let G := both (successorCode x Y W) (candidateCode Y bD p q u t l m r)
  have hsucc : KDerivation (imp D (existsCode Y G)) :=
    fixed_candidate_successor_exists x Y W bD p q d s T u t m r U l R Z V J point
      freshSucc hWc hYc
  have hbase : KDerivation (imp B (allCode Y B)) := schema_vacuity_base t m z Y f hYBase
  have hstep : KDerivation (imp S (allCode Y (imp C L))) := CompactHilbertBasis.identity S
  have hresult : KDerivation (imp F (allCode Y F)) := (CompactNamed.replace t x f).vacuity Y hYInst
  have hlocal := candidate_global_point x Y t u l v m r z w p q uD tD bD aD sD W f
    freshNonempty freshI freshD freshOuter freshAlpha hWx hWY htf hxf hcOthers hcf hYt htv htm hzm
    hmf hvf hvY hvm hvz hvc hrc hrm hrv hwv hwm hpm hpv hpq hqm hqv hpY hqY hmY hvp hvq
    hmGraph hcBase hcStep hcClass
  have hWc : KDerivation (imp G C) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.conjunctionRight (Context.head [] G)
  exact restricted_from_components Y D B S G C L F hsucc hbase hstep hresult hlocal hWc


theorem candidate_restricted_induction_certificate
    (x Y t u l v m r z w p q uD tD bD aD sD W d s T U R Z V J point : Nat)
    (f : CompactNamed.Formula)
    (freshSucc : [x,Y,W,bD,p,q,d,s,T,u,t,m,r,U,l,R,Z,V,J,point].Nodup)
    (hWc : W ≠ adjunctionPredicate x point) (hYc : Y ≠ adjunctionPredicate x point)
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
    (hcClass : filterPredicate Y t (neg f.encode) ∉ (namedAllClassification Y v m z w p q).names)
    (hYBase : Y ∉ (namedAllBase t m z f).names)
    (hYInst : Y ∉ (CompactNamed.replace t x f).names) :
    let inst := (CompactNamed.replace t x f).encode
    let step := allCode Y (imp (candidateCode Y bD p q u t l m r)
      (allStepsCode Y t v m w p q f))
    theoremCode (certificate (candidate_restricted_induction x Y t u l v m r z w p q uD tD bD aD sD W d s T U R Z V J point f
      freshSucc hWc hYc freshNonempty freshI freshD freshOuter freshAlpha hWx hWY htf hxf
      hcOthers hcf hYt htv htm hzm hmf hvf hvY hvm hvz hvc hrc hrm hrv hwv hwm hpm hpv
      hpq hqm hqv hpY hqY hmY hvp hvq hmGraph hcBase hcStep hcClass hYBase hYInst)) =
      imp (candidateCode x bD p q u t l m r)
        (imp (uniformBaseCode t m z f) (imp step inst)) :=
  certificate_correct (candidate_restricted_induction x Y t u l v m r z w p q uD tD bD aD sD W d s T U R Z V J point f
      freshSucc hWc hYc freshNonempty freshI freshD freshOuter freshAlpha hWx hWY htf hxf
      hcOthers hcf hYt htv htm hzm hmf hvf hvY hvm hvz hvc hrc hrm hrv hwv hwm hpm hpv
      hpq hqm hqv hpY hqY hmY hvp hvq hmGraph hcBase hcStep hcClass hYBase hYInst)

end PASoundness.PAtoCompactCandidateRestrictedInduction

#print axioms PASoundness.PAtoCompactCandidateRestrictedInduction.candidate_restricted_induction

#print axioms PASoundness.PAtoCompactCandidateRestrictedInduction.candidate_restricted_induction_certificate
