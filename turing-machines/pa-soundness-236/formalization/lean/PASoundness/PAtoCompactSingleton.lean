import PASoundness.PAtoCompactSingletonSelector
import PASoundness.PAtoCompactAdjunction

/-! Singleton representation from the literal K selector. Every proof retains
finite K derivation data and freshness hypotheses. Singleton outputs need not
be unique; no product collection, quotient or PA interpretation is claimed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSingleton
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactSingletonSelector

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def singletonCode (a s q : Nat) : Nat :=
  allCode q (both (imp (member s q) (equal q a))
    (imp (equal q a) (member s q)))

def namedSingleton (a s q : Nat) : CompactNamed.Formula :=
  .all q (namedBoth (.imp (.member s q) (.equal q a))
    (.imp (.equal q a) (.member s q)))

def namedSingletonInner (a b : Nat) : CompactNamed.Formula :=
  let c := singletonPredicate a b
  namedBoth (.imp (.member a b) (.imp (.equal b a) (.member c b)))
    (.imp (.member c b) (.equal b a))

def namedSingletonBody (a b : Nat) : CompactNamed.Formula :=
  let c := singletonPredicate a b
  namedBoth (.all b (namedSingletonInner a b)) (.imp (.equal b a) (.member c b))

/-- Instantiation of the selector's upper membership bound. -/
def singleton_inner_instance (a b q : Nat) (hba : b ≠ a) (hbq : b ≠ q) :
    KDerivation (imp (allCode b (namedSingletonInner a b).encode)
      (both (imp (member a q) (imp (equal q a) (member (singletonPredicate a b) q)))
        (imp (member (singletonPredicate a b) q) (equal q a)))) := by
  have hc := PAtoCompactSingletonSelector.predicate_names_lt a b
  have hbc : b ≠ singletonPredicate a b := by omega
  have hcb : singletonPredicate a b ≠ b := by omega
  have hcb' : equal b a ≠ b := hcb
  have h := CompactNamed.universalInstance b q (namedSingletonInner a b) hbq
    (by simp [namedSingletonInner, namedBoth, CompactNamed.Formula.binders])
    (by simp [namedSingletonInner, namedBoth, CompactNamed.Formula.binders])
  simpa [namedSingletonInner, namedBoth, singletonPredicate,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.both, CompactProof.neg,
    hba, hbq, hbc, hcb, hcb', Ne.symm hba, Ne.symm hbq, Ne.symm hbc] using h

/-- Under the explicit point equality, the selector witness has singleton
membership at any capture-safe test name. -/
def singleton_pointwise (a b q : Nat) (hba : b ≠ a) (hbq : b ≠ q) :
    KDerivation (imp (singletonBody a b) (imp (equal b a)
      (both (imp (member (singletonPredicate a b) q) (equal q a))
        (imp (equal q a) (member (singletonPredicate a b) q))))) := by
  let c := singletonPredicate a b
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal b a, singletonBody a b]
  have he : Context Γ (equal b a) := .hypothesis (by simp [Γ])
  have hp : Context Γ (singletonBody a b) := .hypothesis (by simp [Γ])
  have hbound : Context Γ (allCode b (namedSingletonInner a b).encode) := by
    have hh := Context.conjunctionLeft hp
    simpa [singletonBody, singletonPredicate, namedSingletonInner, namedBoth,
      CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg] using hh
  have hinst := Context.mp hbound (.closed (singleton_inner_instance a b q hba hbq))
  have hforward : Context Γ (imp (member c q) (equal q a)) := Context.conjunctionRight hinst
  have hma : Context Γ (member c a) := by
    have houter : Context Γ (imp (equal b a) (member c b)) := Context.conjunctionRight hp
    exact .mp he (.mp (.mp he houter) (.closed (memberRightEquality c b a)))
  have hreverse : Context Γ (imp (equal q a) (member c q)) := by
    apply Context.deduction
    have heq : Context (equal q a :: Γ) (equal q a) := Context.head Γ _
    exact .mp (Context.eqSymm heq) (.mp (Context.under hma _) (.closed (memberRightEquality c a q)))
  exact Context.conjunctionIntro hforward hreverse

/-- A selector body and point equality yield its complete singleton graph. -/
def singleton_body_graph (a b q : Nat)
    (hba : b ≠ a) (hqb : q ≠ b) (hqa : q ≠ a) (hqc : q ≠ singletonPredicate a b) :
    KDerivation (imp (singletonBody a b)
      (imp (equal b a) (singletonCode a (singletonPredicate a b) q))) := by
  let c := singletonPredicate a b
  let Γ := [equal b a, singletonBody a b]
  have he : Context Γ (equal b a) := .hypothesis (by simp [Γ])
  have hp : Context Γ (singletonBody a b) := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (both (imp (member c q) (equal q a))
      (imp (equal q a) (member c q))) :=
    .mp he (.mp hp (.closed (singleton_pointwise a b q hba (Ne.symm hqb))))
  let f := namedSingletonBody a b
  have hnames : q ∉ f.names := by
    simp [f, namedSingletonBody, namedSingletonInner, namedBoth,
      CompactNamed.Formula.names, hqb, hqa, hqc]
  have hvBody : KDerivation (imp (singletonBody a b) (allCode q (singletonBody a b))) := by
    have h := f.vacuity q hnames
    simpa [f, namedSingletonBody, namedSingletonInner, namedBoth,
      singletonBody, singletonPredicate, CompactNamed.Formula.encode,
      CompactProof.both, CompactProof.neg] using h
  have hvEq : KDerivation (imp (equal b a) (allCode q (equal b a))) :=
    equalityVacuity b a q hqb hqa
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode q h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases heq : h = equal b a
    · subst h
      exact hvEq
    · have hh' : h = singletonBody a b := hh.resolve_left heq
      subst h
      exact hvBody
  have hgraph : Context Γ (singletonCode a c q) := Context.generalize q hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hgraph

/-- Introduce a concrete singleton witness into a fresh existential binder. -/
def singleton_existential_intro (a c d q : Nat)
    (hcd : c ≠ d) (hda : d ≠ a) (hcq : c ≠ q) (hdq : d ≠ q) :
    KDerivation (imp (singletonCode a c q) (existsCode d (singletonCode a d q))) := by
  let f := namedSingleton a d q
  have h := exists_variable_intro d c f (Ne.symm hcd)
    (by simp [f, namedSingleton, namedBoth, CompactNamed.Formula.binders, hdq])
    (by simp [f, namedSingleton, namedBoth, CompactNamed.Formula.binders, hcq])
  simpa [f, namedSingleton, namedBoth, singletonCode,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.both, CompactProof.neg,
    hcd, hda, hcq, hdq, Ne.symm hcd, Ne.symm hda, Ne.symm hcq, Ne.symm hdq] using h

/-- Exact selector-derived singleton existence with explicit fresh names. -/
def singleton_graph_exists_fresh (a b q d : Nat)
    (hba : b ≠ a) (hqb : q ≠ b) (hqa : q ≠ a) (hqc : q ≠ singletonPredicate a b)
    (hda : d ≠ a) (hdb : d ≠ b) (hdq : d ≠ q) (hdc : d ≠ singletonPredicate a b) :
    KDerivation (existsCode d (singletonCode a d q)) := by
  let c := singletonPredicate a b
  let E := existsCode d (singletonCode a d q)
  let fE : CompactNamed.Formula := .ex d (namedSingleton a d q)
  let fGoal : CompactNamed.Formula := .imp (.equal b a) fE
  have hc := PAtoCompactSingletonSelector.predicate_names_lt a b
  have hca : c ≠ a := by dsimp [c]; omega
  have hcb : c ≠ b := by dsimp [c]; omega
  have hcq : c ≠ q := Ne.symm hqc
  have hcd : c ≠ d := Ne.symm hdc
  have hnamesC : c ∉ fGoal.names := by
    simp [fGoal, fE, namedSingleton, namedBoth, CompactNamed.Formula.names, hca, hcb, hcq, hcd]
  have hvC : KDerivation (imp (imp (equal b a) E) (allCode c (imp (equal b a) E))) := by
    have h := fGoal.vacuity c hnamesC
    simpa [fGoal, fE, E, namedSingleton, namedBoth, singletonCode,
      CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg] using h
  have hbody : KDerivation (imp (singletonBody a b) (imp (equal b a) E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [equal b a, singletonBody a b]
    have he : Context Γ (equal b a) := .hypothesis (by simp [Γ])
    have hp : Context Γ (singletonBody a b) := .hypothesis (by simp [Γ])
    have hs : Context Γ (singletonCode a c q) :=
      .mp he (.mp hp (.closed (singleton_body_graph a b q hba hqb hqa hqc)))
    exact .mp hs (.closed (singleton_existential_intro a c d q hcd hda hcq hdq))
  have hcond : KDerivation (imp (equal b a) E) := by
    apply Context.closeEmpty
    apply Context.existsElim hvC
    · exact .closed (.generalize c hbody)
    · exact .closed (selector8_singleton_witness a b)
  have hnamesB : b ∉ fE.names := by
    simp [fE, namedSingleton, namedBoth, CompactNamed.Formula.names, hba, Ne.symm hdb, Ne.symm hqb]
  have hvB : KDerivation (imp E (allCode b E)) := by
    have h := fE.vacuity b hnamesB
    simpa [fE, E, namedSingleton, namedBoth, singletonCode,
      CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg] using h
  apply Context.closeEmpty
  apply Context.existsElim hvB
  · exact .closed (.generalize b hcond)
  · exact .closed (existsEqual b a)

/-- K constructs a singleton of any input, using concrete fresh labels. -/
def singleton_graph_exists (a : Nat) :
    let b := a+1
    let c := singletonPredicate a b
    let q := c+1
    let d := q+1
    KDerivation (existsCode d (singletonCode a d q)) := by
  dsimp only
  let b := a+1
  let c := singletonPredicate a b
  let q := c+1
  let d := q+1
  have hc := PAtoCompactSingletonSelector.predicate_names_lt a b
  have hba : b ≠ a := by dsimp [b]; omega
  have hqb : q ≠ b := by dsimp [q,c]; omega
  have hqa : q ≠ a := by dsimp [q,c]; omega
  have hqc : q ≠ singletonPredicate a b := by dsimp [q,c]; omega
  have hda : d ≠ a := by dsimp [d,q,c]; omega
  have hdb : d ≠ b := by dsimp [d,q,c]; omega
  have hdq : d ≠ q := by dsimp [d,q]; omega
  have hdc : d ≠ singletonPredicate a b := by dsimp [d,q,c]; omega
  exact singleton_graph_exists_fresh a b q d hba hqb hqa hqc hda hdb hdq hdc

theorem singleton_graph_exists_certificate (a : Nat) :
    let b := a+1
    let c := singletonPredicate a b
    let q := c+1
    let d := q+1
    theoremCode (certificate (singleton_graph_exists a)) = existsCode d (singletonCode a d q) :=
  certificate_correct (singleton_graph_exists a)

end PASoundness.PAtoCompactSingleton

#print axioms PASoundness.PAtoCompactSingleton.singleton_graph_exists
#print axioms PASoundness.PAtoCompactSingleton.singleton_graph_exists_certificate
