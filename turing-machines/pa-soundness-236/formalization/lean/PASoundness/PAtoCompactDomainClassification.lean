import PASoundness.PAtoCompactClassification
import PASoundness.PAtoCompactQuantifiedRefutation

/-! Conditional generalization of local zero-or-predecessor classification.
The outer domain's transitivity and its members' transitivity/greatest-subset
property remain explicit K antecedents. Compact code 1 is literally
`member 0 0`; its ordinary falsity reading is model-dependent. No PA
interpretation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDomainClassification
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactClassification
open PASoundness.PAtoCompactUniformStep PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactLeastCounterexample

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact K alpha conversion between fresh test names for a zero graph. -/
def zero_test_rename (m y z : Nat) (hym : y ≠ m) (hyz : y ≠ z) (hzm : z ≠ m) :
    KDerivation (imp (zeroCode m y) (zeroCode m z)) := by
  let f : CompactNamed.Formula := .imp (.member m y) .bottom
  have h := CompactNamed.universalAlpha y z f hyz
    (by simp [f, CompactNamed.Formula.binders])
    (by simp [f, CompactNamed.Formula.names, hzm, Ne.symm hyz])
  simpa [f, zeroCode, CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.neg, hym, hyz, hzm, Ne.symm hym, Ne.symm hyz, Ne.symm hzm] using h.1

/-- If x is transitive and m∈x, every represented predecessor y∈m lies in x.
The quantifier y is generalized only after proving both context assumptions
vacuous at that name. -/
def predecessor_in_outer_domain (x m p q y w : Nat)
    (hpx : p ≠ x) (hpm : p ≠ m) (hpq : p ≠ q)
    (hqx : q ≠ x) (hqm : q ≠ m) (hqy : q ≠ y)
    (hyx : y ≠ x) (hym : y ≠ m) (hyp : y ≠ p) (hyq : y ≠ q) :
    KDerivation (imp (transitiveCode x p q) (imp (member x m)
      (imp (existsCode y (both (member m y)
          (both (successorCode y m w) (transitiveCode m p q))))
        (existsCode y (both (member x y)
          (both (successorCode y m w) (transitiveCode m p q))))))) := by
  let T := transitiveCode x p q
  let X := member x m
  let A := both (member m y) (both (successorCode y m w) (transitiveCode m p q))
  let B := both (member x y) (both (successorCode y m w) (transitiveCode m p q))
  let Γ := [X,T]
  have hx : Context Γ X := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (imp A B) := by
    apply Context.deduction
    have ha : Context (A :: Γ) A := Context.head Γ A
    have hm : Context (A :: Γ) (member m y) := Context.conjunctionLeft ha
    have hrest : Context (A :: Γ) (both (successorCode y m w) (transitiveCode m p q)) :=
      Context.conjunctionRight ha
    have hy : Context (A :: Γ) (member x y) := .mp hm (.mp (Context.under hx A)
      (.mp (Context.under ht A) (.closed (transitive_chain x p q m y hpx hpm hpq hqx hqm hqy))))
    exact Context.conjunctionIntro hy hrest
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode y h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = X
    · subst h
      exact membershipVacuity x m y hyx hym
    · have he' : h = T := hh.resolve_left he
      subst h
      exact transitive_vacuity x p q y hyx hyp hyq
  have hall : Context Γ (allCode y (imp A B)) := Context.generalize y hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hex : Context (existsCode y A :: Γ) (existsCode y A) := Context.head Γ _
  exact exists_map_context (Context.under hall (existsCode y A)) hex

/-- One member m receives the global-case classification from its own local
transitivity/greatest-subset premise. Outer transitivity ensures its selected
predecessor remains in the outer domain x. -/
def member_classification (x m p q u k y t w z : Nat)
    (fresh : [m,p,q,u,k,y,t,w].Nodup)
    (hpx : p ≠ x) (hqx : q ≠ x)
    (hyx : y ≠ x) (hym : y ≠ m) (hyp : y ≠ p) (hyq : y ≠ q)
    (hyz : y ≠ z) (hzm : z ≠ m) :
    KDerivation (imp (transitiveCode x p q) (imp (member x m)
      (imp (transitiveCode m p q) (imp (greatestSubsetsCode m u k y t)
        (zeroOrPredecessorCore x y m z w p q))))) := by
  have hpm : p ≠ m := by intro h; subst p; simp at fresh
  have hpq : p ≠ q := by intro h; subst p; simp at fresh
  have hqm : q ≠ m := by intro h; subst q; simp at fresh
  have hqy : q ≠ y := by intro h; subst q; simp at fresh
  let T := transitiveCode x p q
  let X := member x m
  let TM := transitiveCode m p q
  let H := greatestSubsetsCode m u k y t
  let Z := zeroCode m y
  let Z' := zeroCode m z
  let E := existsCode y (both (member m y) (both (successorCode y m w) TM))
  let E' := existsCode y (both (member x y) (both (successorCode y m w) TM))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [H,TM,X,T]
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  have hm : Context Γ TM := .hypothesis (by simp [Γ])
  have hx : Context Γ X := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hc : Context Γ (either Z E) := .mp hh (.mp hm (.closed
    (transitive_zero_or_predecessor m p q u k y t w fresh)))
  apply Context.disjunctionElim hc
  · have hz : Context (Z :: Γ) Z := Context.head Γ Z
    have hz' : Context (Z :: Γ) Z' := .mp hz (.closed (zero_test_rename m y z hym hyz hzm))
    exact Context.disjunctionLeft (b := E') hz'
  · have he : Context (E :: Γ) E := Context.head Γ E
    have he' : Context (E :: Γ) E' := .mp he (.mp (Context.under hx E) (.mp (Context.under ht E)
      (.closed (predecessor_in_outer_domain x m p q y w hpx hpm hpq hqx hqm hqy hyx hym hyp hyq))))
    exact Context.disjunctionRight (a := Z') he'

/-- Explicit supplied object-level property: every member m of x is
transitive and has the displayed greatest-subset property. -/
def allMembersDomainCode (x m p q u k y t : Nat) : Nat :=
  allCode m (imp (member x m) (both (transitiveCode m p q) (greatestSubsetsCode m u k y t)))

/-- Pointwise propositional composition used to combine domain-property
instances with the local classification. -/
def domain_pointwise_combine (X TM H C : Nat) :
    KDerivation (imp (imp X (imp TM (imp H C)))
      (imp (imp X (both TM H)) (imp X C))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [X, imp X (both TM H), imp X (imp TM (imp H C))]
  have hx : Context Γ X := .hypothesis (by simp [Γ])
  have hd : Context Γ (imp X (both TM H)) := .hypothesis (by simp [Γ])
  have hl : Context Γ (imp X (imp TM (imp H C))) := .hypothesis (by simp [Γ])
  have hboth : Context Γ (both TM H) := .mp hx hd
  exact .mp (Context.conjunctionRight hboth)
    (.mp (Context.conjunctionLeft hboth) (.mp hx hl))

/-- Quantified classification of every member of x, under explicit outer
transitivity and the supplied domain-property schema. All freshness is on
literal numeric names and ensures both alpha conversion and generalization. -/
def all_members_classification (x m p q u k y t w z : Nat)
    (fresh : [m,p,q,u,k,y,t,w].Nodup)
    (hpx : p ≠ x) (hqx : q ≠ x) (hmx : m ≠ x)
    (hyx : y ≠ x) (hym : y ≠ m) (hyp : y ≠ p) (hyq : y ≠ q)
    (hyz : y ≠ z) (hzm : z ≠ m) :
    KDerivation (imp (transitiveCode x p q) (imp (allMembersDomainCode x m p q u k y t)
      (allClassificationCode x y m z w p q))) := by
  have hmp : m ≠ p := by intro h; subst m; simp at fresh
  have hmq : m ≠ q := by intro h; subst m; simp at fresh
  let T := transitiveCode x p q
  let X := member x m
  let TM := transitiveCode m p q
  let H := greatestSubsetsCode m u k y t
  let C := zeroOrPredecessorCore x y m z w p q
  let D := allMembersDomainCode x m p q u k y t
  let Γ := [D,T]
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hallT : Context Γ (allCode m T) := .mp ht (.closed (transitive_vacuity x p q m hmx hmp hmq))
  have hlocal := member_classification x m p q u k y t w z fresh hpx hqx hyx hym hyp hyq hyz hzm
  have h1 : Context Γ (allCode m (imp X (imp TM (imp H C)))) :=
    Context.allMP hallT (.closed (.generalize m hlocal))
  have h2 : Context Γ (allCode m (imp (imp X (both TM H)) (imp X C))) :=
    Context.allMP h1 (.closed (.generalize m (domain_pointwise_combine X TM H C)))
  have hresult : Context Γ (allClassificationCode x y m z w p q) := Context.allMP hd h2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hresult

theorem all_members_classification_certificate (x m p q u k y t w z : Nat)
    (fresh : [m,p,q,u,k,y,t,w].Nodup)
    (hpx : p ≠ x) (hqx : q ≠ x) (hmx : m ≠ x)
    (hyx : y ≠ x) (hym : y ≠ m) (hyp : y ≠ p) (hyq : y ≠ q)
    (hyz : y ≠ z) (hzm : z ≠ m) :
    theoremCode (certificate (all_members_classification x m p q u k y t w z
      fresh hpx hqx hmx hyx hym hyp hyq hyz hzm)) =
      imp (transitiveCode x p q) (imp (allMembersDomainCode x m p q u k y t)
        (allClassificationCode x y m z w p q)) :=
  certificate_correct (all_members_classification x m p q u k y t w z
    fresh hpx hqx hmx hyx hym hyp hyq hyz hzm)

/-- Conditional predicate instance with the classification schema discharged
by outer transitivity and the supplied all-members domain-property schema.
Base, step, domain-property and least-subset conditions remain K antecedents. -/
def domain_conditioned_induction_instance
    (x t a u y m r z w p q uD kD tD : Nat) (f : CompactNamed.Formula)
    (freshI : [x,t,a,u,m,r].Nodup) (freshD : [m,p,q,uD,kD,y,tD,w].Nodup)
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
    KDerivation (imp (transitiveCode x p q) (imp (allMembersDomainCode x m p q uD kD y tD)
      (imp (uniformBaseCode t m z f) (imp (allStepsCode x t y m w p q f)
        (imp (leastSubsetsCode x u t a m r) (imp (member x a) inst)))))) := by
  dsimp only
  let T := transitiveCode x p q
  let D := allMembersDomainCode x m p q uD kD y tD
  let B := uniformBaseCode t m z f
  let S := allStepsCode x t y m w p q f
  let C := allClassificationCode x y m z w p q
  let Γ := [S,B,D,T]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .mp hd (.mp ht (.closed
    (all_members_classification x m p q uD kD y tD w z freshD hpx hqx hmx
      hyx hym hyp hyq hyz hzm)))
  have hi := conditional_induction_instance x t a u y m r z w p q f
    freshI htf haf hcOthers hcf hxt hty htm hzm hmf hyf hyx hym hyz hyc hrc hrm hry
    hwy hwm hpm hpy hpq hqm hqy hmGraph hcBase hcStep hcClass
  have hout := Context.mp hc (.mp hs (.mp hb (.closed hi)))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hout

theorem domain_conditioned_induction_certificate
    (x t a u y m r z w p q uD kD tD : Nat) (f : CompactNamed.Formula)
    (freshI : [x,t,a,u,m,r].Nodup) (freshD : [m,p,q,uD,kD,y,tD,w].Nodup)
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
    theoremCode (certificate (domain_conditioned_induction_instance
      x t a u y m r z w p q uD kD tD f freshI freshD htf haf hcOthers hcf hxt hty htm hzm hmf hyf
      hyx hym hyz hyc hrc hrm hry hwy hwm hpm hpy hpq hqm hqy hpx hqx hmx hyp hyq
      hmGraph hcBase hcStep hcClass)) =
      imp (transitiveCode x p q) (imp (allMembersDomainCode x m p q uD kD y tD)
        (imp (uniformBaseCode t m z f) (imp (allStepsCode x t y m w p q f)
          (imp (leastSubsetsCode x u t a m r) (imp (member x a) inst))))) :=
  certificate_correct (domain_conditioned_induction_instance
    x t a u y m r z w p q uD kD tD f freshI freshD htf haf hcOthers hcf hxt hty htm hzm hmf hyf
    hyx hym hyz hyc hrc hrm hry hwy hwm hpm hpy hpq hqm hqy hpx hqx hmx hyp hyq
    hmGraph hcBase hcStep hcClass)

end PASoundness.PAtoCompactDomainClassification
