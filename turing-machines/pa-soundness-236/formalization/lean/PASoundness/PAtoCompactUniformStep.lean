import PASoundness.PAtoCompactExistentialCases
import PASoundness.PAtoCompactTransitiveWitness

/-! Explicit quantified preservation premise and its existential K lifting.
This does not establish the premise, a domain, classification, or induction.
Code 1 is literally `member 0 0`; ordinary falsity is model-dependent. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactUniformStep
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactCounterexampleSet
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactExistentialCases
open PASoundness.PAtoCompactTransitiveWitness

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact predecessor-domain core, before supplying a preservation step. -/
def predecessorCore (x y m w p q : Nat) : Nat :=
  both (member x y) (both (successorCode y m w) (transitiveCode m p q))

/-- The explicitly supplied uniform preservation schema: for every y satisfying
the predecessor-domain core, the capture-safe f(y) code implies f(m). -/
def uniformStepCode (x t y m w p q : Nat) (f : CompactNamed.Formula) : Nat :=
  allCode y (imp (predecessorCore x y m w p q)
    (imp (CompactNamed.replace t y f).encode (CompactNamed.replace t m f).encode))

/-- The classification before strengthening: zero, or some predecessor
enjoying the explicitly displayed domain/successor/transitivity properties. -/
def zeroOrPredecessorCore (x y m z w p q : Nat) : Nat :=
  either (zeroCode m z) (existsCode y (predecessorCore x y m w p q))

def namedPredecessorCore (x y m w p q : Nat) : CompactNamed.Formula :=
  namedBoth (.member x y)
    (namedBoth (.all w (namedSuccessorBody y m w)) (.all p (.all q (transitiveBody m p q))))

def namedUniformStepBody (x t y m w p q : Nat) (f : CompactNamed.Formula) : CompactNamed.Formula :=
  .imp (namedPredecessorCore x y m w p q)
    (.imp (CompactNamed.replace t y f) (CompactNamed.replace t m f))

/-- K derives the named instance of the supplied schema. The predecessor name
y is absent from all internal binders; predicate replacement is capture-safe. -/
def uniform_step_instance (x t y m w p q : Nat) (f : CompactNamed.Formula)
    (hyw : y ≠ w) (hyp : y ≠ p) (hyq : y ≠ q) (hyf : y ∉ f.names)
    (_hyx : y ≠ x) (_hym : y ≠ m) (_hty : t ≠ y)
    (_htf : t ∉ f.binders) (_hmf : m ∉ f.binders) :
    KDerivation (imp (uniformStepCode x t y m w p q f)
      (imp (predecessorCore x y m w p q)
        (imp (CompactNamed.replace t y f).encode (CompactNamed.replace t m f).encode))) := by
  let body := namedUniformStepBody x t y m w p q f
  have hyb : y ∉ f.binders := fun h => hyf (f.binders_subset_names h)
  have hy : y ∉ body.binders := by
    simp [body, namedUniformStepBody, namedPredecessorCore, namedBoth,
      namedSuccessorBody, namedEither, transitiveBody, CompactNamed.Formula.binders,
      CompactNamed.replace_binders, hyw, hyp, hyq, hyb]
  have h := CompactNamed.allSpecialize y body hy
  simpa [body, namedUniformStepBody, namedPredecessorCore, namedBoth, namedSuccessorBody,
    namedEither, transitiveBody, uniformStepCode, predecessorCore, successorCode, transitiveCode,
    CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using h

/-- Under the uniform schema, each existential core witness can be retained
with the corresponding local step attached, using K existential monotonicity. -/
def attach_uniform_step (x t y m w p q : Nat) (f : CompactNamed.Formula) :
    KDerivation (imp (uniformStepCode x t y m w p q f)
      (imp (existsCode y (predecessorCore x y m w p q))
        (existsCode y (predecessorBranch x t y m w p q f)))) := by
  let D := predecessorCore x y m w p q
  let fy := (CompactNamed.replace t y f).encode
  let fm := (CompactNamed.replace t m f).encode
  let H := imp fy fm
  let D' := predecessorBranch x t y m w p q f
  let U := uniformStepCode x t y m w p q f
  have hpoint : KDerivation (imp (imp D H) (imp D D')) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [D, imp D H]
    have hd : Context Γ D := .hypothesis (by simp [Γ])
    have hh : Context Γ (imp D H) := .hypothesis (by simp [Γ])
    have hx := Context.conjunctionLeft hd
    have hst := Context.conjunctionRight hd
    have hs := Context.conjunctionLeft hst
    have ht := Context.conjunctionRight hst
    exact Context.conjunctionIntro hx (Context.conjunctionIntro hs
      (Context.conjunctionIntro ht (.mp hd hh)))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [existsCode y D, U]
  have hex : Context Γ (existsCode y D) := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hmap : Context Γ (allCode y (imp D D')) :=
    Context.allMP hu (.closed (.generalize y hpoint))
  exact exists_map_context hmap hex

/-- An existential predecessor classification plus the quantified step
implies the predecessor classification carrying the local step explicitly. -/
def classify_with_uniform_step (x t y m z w p q : Nat) (f : CompactNamed.Formula) :
    KDerivation (imp (uniformStepCode x t y m w p q f)
      (imp (zeroOrPredecessorCore x y m z w p q)
        (zeroOrExistentialPredecessor x t y m z w p q f))) := by
  let U := uniformStepCode x t y m w p q f
  let Z := zeroCode m z
  let E := existsCode y (predecessorCore x y m w p q)
  let E' := existsCode y (predecessorBranch x t y m w p q f)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [either Z E, U]
  have hc : Context Γ (either Z E) := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  apply Context.disjunctionElim hc
  · exact Context.disjunctionLeft (b := E') (Context.head Γ Z)
  · have he : Context (E :: Γ) E := Context.head Γ E
    have hu' : Context (E :: Γ) U := Context.under hu E
    have he' : Context (E :: Γ) E' := .mp he (.mp hu' (.closed (attach_uniform_step x t y m w p q f)))
    exact Context.disjunctionRight (a := Z) he'

/-- Under the explicit quantified preservation schema and an existential
predecessor-or-zero classification, the existing local case proof yields
literal code 1. Leastness, the classification, the base, and preservation
remain supplied object-level hypotheses. -/
def uniform_step_cases (x t y m r z w p q : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m) (hzm : z ≠ m)
    (htf : t ∉ f.binders) (hmf : m ∉ f.binders) (hyf : y ∉ f.names)
    (hyx : y ≠ x) (hym : y ≠ m) (hyz : y ≠ z)
    (hyc : y ≠ filterPredicate x t (neg f.encode))
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y) :
    let c := filterPredicate x t (neg f.encode)
    let fm := (CompactNamed.replace t m f).encode
    KDerivation (imp (filterGraph x c t (neg f.encode)) (imp (leastMemberCode c m r)
      (imp (uniformStepCode x t y m w p q f) (imp (zeroOrPredecessorCore x y m z w p q)
        (imp (imp (zeroCode m z) fm) 1))))) := by
  dsimp only
  let c := filterPredicate x t (neg f.encode)
  let fm := (CompactNamed.replace t m f).encode
  let G := filterGraph x c t (neg f.encode)
  let L := leastMemberCode c m r
  let U := uniformStepCode x t y m w p q f
  let C := zeroOrPredecessorCore x y m z w p q
  let B := imp (zeroCode m z) fm
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [B,C,U,L,G]
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hl : Context Γ L := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hc' : Context Γ (zeroOrExistentialPredecessor x t y m z w p q f) :=
    .mp hc (.mp hu (.closed (classify_with_uniform_step x t y m z w p q f)))
  exact .mp hb (.mp hc' (.mp hl (.mp hg
    (.closed (existential_predecessor_cases x t y m r z w p q f hxt hty htm hzm
      htf hmf hyf hyx hym hyz hyc hrc hrm hry hwy hwm hpm hpy hpq hqm hqy)))))

theorem uniform_step_cases_certificate (x t y m r z w p q : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m) (hzm : z ≠ m)
    (htf : t ∉ f.binders) (hmf : m ∉ f.binders) (hyf : y ∉ f.names)
    (hyx : y ≠ x) (hym : y ≠ m) (hyz : y ≠ z)
    (hyc : y ≠ filterPredicate x t (neg f.encode))
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y) :
    let c := filterPredicate x t (neg f.encode)
    let fm := (CompactNamed.replace t m f).encode
    theoremCode (certificate (uniform_step_cases x t y m r z w p q f hxt hty htm hzm
      htf hmf hyf hyx hym hyz hyc hrc hrm hry hwy hwm hpm hpy hpq hqm hqy)) =
      imp (filterGraph x c t (neg f.encode)) (imp (leastMemberCode c m r)
        (imp (uniformStepCode x t y m w p q f) (imp (zeroOrPredecessorCore x y m z w p q)
          (imp (imp (zeroCode m z) fm) 1)))) :=
  certificate_correct (uniform_step_cases x t y m r z w p q f hxt hty htm hzm
    htf hmf hyf hyx hym hyz hyc hrc hrm hry hwy hwm hpm hpy hpq hqm hqy)

/-- In standard HF semantics, the quantified step has the advertised named
predicate reading: the original f is evaluated with t set to the predecessor
and successor values. The fresh predecessor binder y cannot capture any
pre-existing free or bound name of f. -/
theorem uniform_step_standard (x t y m w p q : Nat) (f : CompactNamed.Formula)
    (hty : t ≠ y) (hym : y ≠ m) (hyf : y ∉ f.names)
    (htf : t ∉ f.binders) (hmf : m ∉ f.binders) (ρ : CompactMatrix.Environment) :
    (CompactMatrix.decode (uniformStepCode x t y m w p q f)).Realize ρ ↔
      ∀ v, (CompactMatrix.decode (predecessorCore x y m w p q)).Realize (CompactMatrix.update ρ y v) →
        (f.Realize (CompactMatrix.update ρ t v) → f.Realize (CompactMatrix.update ρ t (ρ m))) := by
  have hyb : y ∉ f.binders := fun h => hyf (f.binders_subset_names h)
  rw [uniformStepCode, CompactSemantics.realize_all]
  apply forall_congr'
  intro v
  rw [CompactSemantics.realize_imp, CompactSemantics.realize_imp,
    CompactNamed.Formula.encode_realize, CompactNamed.Formula.encode_realize,
    CompactNamed.replace_realize t y f htf hyb (CompactMatrix.update ρ y v),
    CompactNamed.replace_realize t m f htf hmf (CompactMatrix.update ρ y v)]
  simp only [CompactSemantics.update_same,
    CompactSemantics.update_other ρ y m v (Ne.symm hym)]
  have hfirst : f.Realize (CompactMatrix.update (CompactMatrix.update ρ y v) t v) ↔
      f.Realize (CompactMatrix.update ρ t v) := by
    rw [CompactSemantics.update_commute ρ y t v v (Ne.symm hty)]
    exact CompactNamed.Formula.realize_update_fresh f _ y v hyf
  have hsecond : f.Realize (CompactMatrix.update (CompactMatrix.update ρ y v) t (ρ m)) ↔
      f.Realize (CompactMatrix.update ρ t (ρ m)) := by
    rw [CompactSemantics.update_commute ρ y t v (ρ m) (Ne.symm hty)]
    exact CompactNamed.Formula.realize_update_fresh f _ y v hyf
  exact imp_congr Iff.rfl (imp_congr hfirst hsecond)

end PASoundness.PAtoCompactUniformStep
