import PASoundness.PAtoCompactUniformBase
import PASoundness.PAtoCompactInductionCases

/-! A conditional K refutation under explicitly supplied object-level base,
step, classification, and least-subset hypotheses. No K proof of those
hypotheses, general induction, or PA interpretation is asserted. Compact
code 1 is literally `member 0 0`; its falsity reading is model-dependent. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactCounterexampleSet
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactUniformBase PASoundness.PAtoCompactInductionCases

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Supplied step schema for every possible least member m. -/
def allStepsCode (x t y m w p q : Nat) (f : CompactNamed.Formula) : Nat :=
  allCode m (uniformStepCode x t y m w p q f)

/-- Supplied classification only for elements of x: zero, or an in-domain
predecessor with the specified successor and transitivity conditions. -/
def allClassificationCode (x y m z w p q : Nat) : Nat :=
  allCode m (imp (member x m) (zeroOrPredecessorCore x y m z w p q))

def namedAllSteps (x t y m w p q : Nat) (f : CompactNamed.Formula) : CompactNamed.Formula :=
  .all m (.all y (namedUniformStepBody x t y m w p q f))

def namedAllClassification (x y m z w p q : Nat) : CompactNamed.Formula :=
  .all m (.imp (.member x m)
    (namedEither (.all z (.imp (.member m z) .bottom))
      (.ex y (namedPredecessorCore x y m w p q))))

def namedAllBase (t m z : Nat) (f : CompactNamed.Formula) : CompactNamed.Formula :=
  .all m (namedUniformBaseBody t m z f)

def namedFilterGraph (x t : Nat) (f : CompactNamed.Formula) : CompactNamed.Formula :=
  .all t (namedCounterexampleGraphBody x t f)

/-- A closed pointwise K refutation with the membership needed to apply the
classification extracted from the exact counterexample graph. -/
def pointwise_refutation (x t y m r z w p q : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m) (hzm : z ≠ m)
    (htf : t ∉ f.binders) (hmf : m ∉ f.names) (hyf : y ∉ f.names)
    (hyx : y ≠ x) (hym : y ≠ m) (hyz : y ≠ z)
    (hyc : y ≠ filterPredicate x t (neg f.encode))
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y) :
    let c := filterPredicate x t (neg f.encode)
    let fm := (CompactNamed.replace t m f).encode
    let G := filterGraph x c t (neg f.encode)
    let L := leastMemberCode c m r
    let U := uniformStepCode x t y m w p q f
    let C := zeroOrPredecessorCore x y m z w p q
    KDerivation (imp G (imp U (imp (imp (member x m) C)
      (imp (imp (zeroCode m z) fm) (neg L))))) := by
  dsimp only
  let c := filterPredicate x t (neg f.encode)
  let fm := (CompactNamed.replace t m f).encode
  let G := filterGraph x c t (neg f.encode)
  let L := leastMemberCode c m r
  let U := uniformStepCode x t y m w p q f
  let C := zeroOrPredecessorCore x y m z w p q
  let B := imp (zeroCode m z) fm
  let H := imp (member x m) C
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [L,B,H,U,G]
  have hl : Context Γ L := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hmf' : m ∉ f.binders := fun h => hmf (f.binders_subset_names h)
  have hgraph := Context.mp hg (.closed (counterexample_graph_at x t m f hxt htm htf hmf'))
  have hm : Context Γ (member c m) := Context.conjunctionLeft hl
  have hx : Context Γ (member x m) := Context.conjunctionLeft (.mp hm (Context.conjunctionLeft hgraph))
  have hc : Context Γ C := .mp hx hh
  exact .mp hb (.mp hc (.mp hu (.mp hl (.mp hg
    (.closed (uniform_step_cases x t y m r z w p q f hxt hty htm hzm htf hmf' hyf
      hyx hym hyz hyc hrc hrm hry hwy hwm hpm hpy hpq hqm hqy))))))

/-- The named schemas encode to the exact literal K codes used below. -/
@[simp] theorem named_all_base_encode (t m z : Nat) (f : CompactNamed.Formula) :
    (namedAllBase t m z f).encode = uniformBaseCode t m z f := by
  simp [namedAllBase, namedUniformBaseBody, uniformBaseCode, zeroCode,
    CompactNamed.Formula.encode, CompactProof.neg]

@[simp] theorem named_all_steps_encode (x t y m w p q : Nat) (f : CompactNamed.Formula) :
    (namedAllSteps x t y m w p q f).encode = allStepsCode x t y m w p q f := by
  simp [namedAllSteps, namedUniformStepBody, namedPredecessorCore, namedBoth, namedSuccessorBody,
    namedEither, transitiveBody, allStepsCode, uniformStepCode, predecessorCore, successorCode,
    transitiveCode, CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg,
    CompactDerivations.either]

@[simp] theorem named_all_classification_encode (x y m z w p q : Nat) :
    (namedAllClassification x y m z w p q).encode = allClassificationCode x y m z w p q := by
  simp [namedAllClassification, namedPredecessorCore, namedBoth, namedSuccessorBody, namedEither,
    transitiveBody, allClassificationCode, zeroOrPredecessorCore, predecessorCore, successorCode,
    transitiveCode, zeroCode, CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg,
    CompactDerivations.either]

@[simp] theorem named_filter_graph_encode (x t : Nat) (f : CompactNamed.Formula) :
    (namedFilterGraph x t f).encode = filterGraph x (filterPredicate x t (neg f.encode)) t (neg f.encode) := by
  simp [namedFilterGraph, namedCounterexampleGraphBody, namedBoth, CompactNamed.Formula.not,
    filterGraph, filterPredicate, CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg]

/-- Explicit supplied global schemas are vacuous at a fresh filter-witness
name. These are finite K derivations, not semantic generalization. -/
def schema_vacuity_base (t m z c : Nat) (f : CompactNamed.Formula)
    (h : c ∉ (namedAllBase t m z f).names) :
    KDerivation (imp (uniformBaseCode t m z f) (allCode c (uniformBaseCode t m z f))) := by
  simpa only [named_all_base_encode] using (namedAllBase t m z f).vacuity c h

def schema_vacuity_steps (x t y m w p q c : Nat) (f : CompactNamed.Formula)
    (h : c ∉ (namedAllSteps x t y m w p q f).names) :
    KDerivation (imp (allStepsCode x t y m w p q f) (allCode c (allStepsCode x t y m w p q f))) := by
  simpa only [named_all_steps_encode] using (namedAllSteps x t y m w p q f).vacuity c h

def schema_vacuity_classification (x y m z w p q c : Nat)
    (h : c ∉ (namedAllClassification x y m z w p q).names) :
    KDerivation (imp (allClassificationCode x y m z w p q)
      (allCode c (allClassificationCode x y m z w p q))) := by
  simpa only [named_all_classification_encode] using (namedAllClassification x y m z w p q).vacuity c h

def graph_vacuity (x t m : Nat) (f : CompactNamed.Formula)
    (h : m ∉ (namedFilterGraph x t f).names) :
    KDerivation (imp (filterGraph x (filterPredicate x t (neg f.encode)) t (neg f.encode))
      (allCode m (filterGraph x (filterPredicate x t (neg f.encode)) t (neg f.encode)))) := by
  simpa only [named_filter_graph_encode] using (namedFilterGraph x t f).vacuity m h

/-- The three supplied object-level global schemas refute every represented
least-counterexample witness. Classification is required only for members of
x. Freshness of the graph and schemas is explicit syntax, and no schema is
claimed as a K theorem. -/
def universal_witness_refutation (x t y m r z w p q : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m) (hzm : z ≠ m)
    (htf : t ∉ f.binders) (hmf : m ∉ f.names) (hyf : y ∉ f.names)
    (hyx : y ≠ x) (hym : y ≠ m) (hyz : y ≠ z)
    (hyc : y ≠ filterPredicate x t (neg f.encode))
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y)
    (hmGraph : m ∉ (namedFilterGraph x t f).names)
    (hcBase : filterPredicate x t (neg f.encode) ∉ (namedAllBase t m z f).names)
    (hcStep : filterPredicate x t (neg f.encode) ∉ (namedAllSteps x t y m w p q f).names)
    (hcClass : filterPredicate x t (neg f.encode) ∉ (namedAllClassification x y m z w p q).names) :
    let c := filterPredicate x t (neg f.encode)
    let G := filterGraph x c t (neg f.encode)
    let L := leastMemberCode c m r
    KDerivation (imp (uniformBaseCode t m z f) (imp (allStepsCode x t y m w p q f)
      (imp (allClassificationCode x y m z w p q) (allCode c (neg (both G (existsCode m L))))))) := by
  dsimp only
  let c := filterPredicate x t (neg f.encode)
  let fm := (CompactNamed.replace t m f).encode
  let G := filterGraph x c t (neg f.encode)
  let L := leastMemberCode c m r
  let U := uniformStepCode x t y m w p q f
  let C := zeroOrPredecessorCore x y m z w p q
  let B := uniformBaseCode t m z f
  let S := allStepsCode x t y m w p q f
  let K := allClassificationCode x y m z w p q
  let A := both G (existsCode m L)
  let Γ := [K,S,B]
  have hk : Context Γ K := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hnot : Context Γ (neg A) := by
    apply Context.deduction
    let Δ := A :: Γ
    have ha : Context Δ A := Context.head Γ A
    have hg : Context Δ G := Context.conjunctionLeft ha
    have hex : Context Δ (existsCode m L) := Context.conjunctionRight ha
    have hallG : Context Δ (allCode m G) := .mp hg (.closed (graph_vacuity x t m f hmGraph))
    have hlocal := pointwise_refutation x t y m r z w p q f hxt hty htm hzm htf hmf hyf
      hyx hym hyz hyc hrc hrm hry hwy hwm hpm hpy hpq hqm hqy
    have h1 := Context.allMP hallG (.closed (.generalize m hlocal))
    have h2 := Context.allMP (Context.under hs A) h1
    have h3 := Context.allMP (Context.under hk A) h2
    have h4 : Context Δ (allCode m (neg L)) := Context.allMP (Context.under hb A) h3
    exact .mp h4 hex
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode c h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases h1 : h = K
    · subst h
      exact schema_vacuity_classification x y m z w p q c hcClass
    · by_cases h2 : h = S
      · subst h
        exact schema_vacuity_steps x t y m w p q c f hcStep
      · have h3 : h = B := ((hh.resolve_left h1).resolve_left h2)
        subst h
        exact schema_vacuity_base t m z c f hcBase
  have hall : Context Γ (allCode c (neg A)) := Context.generalize c hv hnot
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hall

/-- Conditional refutation of an explicit in-domain counterexample, assembled
from the object-level base, step, domain classification and least-subset
schemas. All those schemas remain premises; this is not a theorem that they
hold, nor a PA interpretation. -/
def conditional_counterexample_refutation (x t a u y m r z w p q : Nat) (f : CompactNamed.Formula)
    (fresh : [x,t,a,u,m,r].Nodup) (htf : t ∉ f.binders) (haf : a ∉ f.binders)
    (hcOthers : filterPredicate x t (neg f.encode) ∉ [a,u,m,r])
    (hcf : filterPredicate x t (neg f.encode) ∉ f.names)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m) (hzm : z ≠ m)
    (hmf : m ∉ f.names) (hyf : y ∉ f.names)
    (hyx : y ≠ x) (hym : y ≠ m) (hyz : y ≠ z)
    (hyc : y ≠ filterPredicate x t (neg f.encode))
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y)
    (hmGraph : m ∉ (namedFilterGraph x t f).names)
    (hcBase : filterPredicate x t (neg f.encode) ∉ (namedAllBase t m z f).names)
    (hcStep : filterPredicate x t (neg f.encode) ∉ (namedAllSteps x t y m w p q f).names)
    (hcClass : filterPredicate x t (neg f.encode) ∉ (namedAllClassification x y m z w p q).names) :
    let inst := (CompactNamed.replace t a f).encode
    KDerivation (imp (uniformBaseCode t m z f) (imp (allStepsCode x t y m w p q f)
      (imp (allClassificationCode x y m z w p q) (imp (leastSubsetsCode x u t a m r)
        (imp (member x a) (imp (neg inst) 1)))))) := by
  dsimp only
  let B := uniformBaseCode t m z f
  let S := allStepsCode x t y m w p q f
  let K := allClassificationCode x y m z w p q
  let Γ := [K,S,B]
  have hk : Context Γ K := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  let c := filterPredicate x t (neg f.encode)
  let G := filterGraph x c t (neg f.encode)
  let L := leastMemberCode c m r
  let A := both G (existsCode m L)
  have hall : Context Γ (allCode c (neg A)) := .mp hk (.mp hs (.mp hb (.closed
    (universal_witness_refutation x t y m r z w p q f hxt hty htm hzm htf hmf hyf
      hyx hym hyz hyc hrc hrm hry hwy hwm hpm hpy hpq hqm hqy hmGraph hcBase hcStep hcClass))))
  have hresult := Context.mp hall (.closed (refute_counterexample_from_universal x t a u m r f
    fresh htf haf hcOthers hcf))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hresult

/-- Finite propositional conversion of conditional counterexample refutation
to the corresponding positive predicate instance. -/
def refutation_to_instance {B S K L X F : Nat}
    (h : KDerivation (imp B (imp S (imp K (imp L (imp X (neg (neg F)))))))) :
    KDerivation (imp B (imp S (imp K (imp L (imp X F))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [X,L,K,S,B]
  have hx : Context Γ X := .hypothesis (by simp [Γ])
  have hl : Context Γ L := .hypothesis (by simp [Γ])
  have hk : Context Γ K := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  apply Context.dne
  exact .mp hx (.mp hl (.mp hk (.mp hs (.mp hb (.closed h)))))

/-- Conditional K predicate instance under the explicit quantified base,
step, in-domain classification, and least-subset hypotheses. The theorem
constructs literal proof data; it does not establish those hypotheses. -/
def conditional_induction_instance (x t a u y m r z w p q : Nat) (f : CompactNamed.Formula)
    (fresh : [x,t,a,u,m,r].Nodup) (htf : t ∉ f.binders) (haf : a ∉ f.binders)
    (hcOthers : filterPredicate x t (neg f.encode) ∉ [a,u,m,r])
    (hcf : filterPredicate x t (neg f.encode) ∉ f.names)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m) (hzm : z ≠ m)
    (hmf : m ∉ f.names) (hyf : y ∉ f.names)
    (hyx : y ≠ x) (hym : y ≠ m) (hyz : y ≠ z)
    (hyc : y ≠ filterPredicate x t (neg f.encode))
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y)
    (hmGraph : m ∉ (namedFilterGraph x t f).names)
    (hcBase : filterPredicate x t (neg f.encode) ∉ (namedAllBase t m z f).names)
    (hcStep : filterPredicate x t (neg f.encode) ∉ (namedAllSteps x t y m w p q f).names)
    (hcClass : filterPredicate x t (neg f.encode) ∉ (namedAllClassification x y m z w p q).names) :
    let inst := (CompactNamed.replace t a f).encode
    KDerivation (imp (uniformBaseCode t m z f) (imp (allStepsCode x t y m w p q f)
      (imp (allClassificationCode x y m z w p q) (imp (leastSubsetsCode x u t a m r)
        (imp (member x a) inst))))) :=
  refutation_to_instance (conditional_counterexample_refutation x t a u y m r z w p q f
    fresh htf haf hcOthers hcf hxt hty htm hzm hmf hyf hyx hym hyz hyc hrc hrm hry
    hwy hwm hpm hpy hpq hqm hqy hmGraph hcBase hcStep hcClass)

theorem conditional_induction_instance_certificate (x t a u y m r z w p q : Nat) (f : CompactNamed.Formula)
    (fresh : [x,t,a,u,m,r].Nodup) (htf : t ∉ f.binders) (haf : a ∉ f.binders)
    (hcOthers : filterPredicate x t (neg f.encode) ∉ [a,u,m,r])
    (hcf : filterPredicate x t (neg f.encode) ∉ f.names)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m) (hzm : z ≠ m)
    (hmf : m ∉ f.names) (hyf : y ∉ f.names)
    (hyx : y ≠ x) (hym : y ≠ m) (hyz : y ≠ z)
    (hyc : y ≠ filterPredicate x t (neg f.encode))
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y)
    (hmGraph : m ∉ (namedFilterGraph x t f).names)
    (hcBase : filterPredicate x t (neg f.encode) ∉ (namedAllBase t m z f).names)
    (hcStep : filterPredicate x t (neg f.encode) ∉ (namedAllSteps x t y m w p q f).names)
    (hcClass : filterPredicate x t (neg f.encode) ∉ (namedAllClassification x y m z w p q).names) :
    let inst := (CompactNamed.replace t a f).encode
    theoremCode (certificate (conditional_induction_instance x t a u y m r z w p q f
      fresh htf haf hcOthers hcf hxt hty htm hzm hmf hyf hyx hym hyz hyc hrc hrm hry
      hwy hwm hpm hpy hpq hqm hqy hmGraph hcBase hcStep hcClass)) =
      imp (uniformBaseCode t m z f) (imp (allStepsCode x t y m w p q f)
        (imp (allClassificationCode x y m z w p q) (imp (leastSubsetsCode x u t a m r)
          (imp (member x a) inst)))) :=
  certificate_correct (conditional_induction_instance x t a u y m r z w p q f
    fresh htf haf hcOthers hcf hxt hty htm hzm hmf hyf hyx hym hyz hyc hrc hrm hry
    hwy hwm hpm hpy hpq hqm hqy hmGraph hcBase hcStep hcClass)

/-- Separate standard-HF meaning of the final named predicate instance;
this semantic equivalence is not used to construct the K derivation. -/
theorem predicate_instance_standard (t a : Nat) (f : CompactNamed.Formula)
    (htf : t ∉ f.binders) (haf : a ∉ f.binders) (ρ : CompactMatrix.Environment) :
    (CompactMatrix.decode (CompactNamed.replace t a f).encode).Realize ρ ↔
      f.Realize (CompactMatrix.update ρ t (ρ a)) := by
  rw [CompactNamed.Formula.encode_realize, CompactNamed.replace_realize t a f htf haf ρ]

end PASoundness.PAtoCompactQuantifiedRefutation
