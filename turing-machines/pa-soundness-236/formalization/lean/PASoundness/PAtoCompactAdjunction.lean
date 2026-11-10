import PASoundness.PAtoCompactTransitiveClosure

/-! Literal selector-8 comprehension specialized to the successor predicate,
constructing a successor-graph witness with explicit fresh names. This does not
establish unique representatives or a PA interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdjunction
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor

/-- Predicate for a candidate member b of the successor of a: b=a or b∈a.
The numeric formula code is also selector 8's witness variable name. -/
def adjunctionPredicate (a b : Nat) : Nat :=
  either (equal b a) (member a b)

/-- Exact selector-8 body, retaining its quantified element variable and the
outside occurrence of the selected point b. -/
def adjunctionBody (a b : Nat) : Nat :=
  let c := adjunctionPredicate a b
  both (allCode b (both
      (imp (member a b) (imp c (member c b)))
      (imp (member c b) c)))
    (imp c (member c b))

/-- The formula code strictly exceeds both input names, so neither selector-8
guard branch collides with the witness variable. -/
theorem predicate_names_lt (a b : Nat) : a < adjunctionPredicate a b ∧ b < adjunctionPredicate a b := by
  have hleft := Cantor.left_le_pair a b
  have hright := Cantor.right_le_pair a b
  have hpair := Cantor.right_le_pair (neg (equal b a)) (member a b)
  unfold adjunctionPredicate either imp member at *
  omega

/-- An existing member meets the candidate predicate, with actual finite K
proof data. -/
def predicate_of_member (a b : Nat) : KDerivation (imp (member a b) (adjunctionPredicate a b)) := by
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.disjunctionRight (a := equal b a) (Context.head [] (member a b))

/-- The designated input itself meets the candidate predicate. -/
def predicate_of_equal (a b : Nat) : KDerivation (imp (equal b a) (adjunctionPredicate a b)) := by
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.disjunctionLeft (b := member a b) (Context.head [] (equal b a))

/-- Selector 8 constructively supplies the precise filtered-comprehension
witness for the candidate successor predicate. No semantic model or soundness
result is used. The result does not yet assert that the body is the full
successor graph. -/
def selector8_adjunction_witness (a b : Nat) :
    KDerivation (existsCode (adjunctionPredicate a b) (adjunctionBody a b)) := by
  let c := adjunctionPredicate a b
  have hc := predicate_names_lt a b
  have hguard : ¬ (c = a ∨ c = b) := by dsimp [c]; omega
  have h := KDerivation.axiom (⟨8, by decide⟩ : Fin 9) a b c 0
  simp only [axiomCode, if_neg hguard] at h
  exact Context.closeEmpty (Context.conjunctionLeft (.closed h))

theorem selector8_adjunction_certificate (a b : Nat) :
    theoremCode (certificate (selector8_adjunction_witness a b)) =
      existsCode (adjunctionPredicate a b) (adjunctionBody a b) :=
  certificate_correct (selector8_adjunction_witness a b)

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def namedPredicate (a b : Nat) : CompactNamed.Formula :=
  namedEither (.equal b a) (.member a b)

def namedAdjunctionInner (a b : Nat) : CompactNamed.Formula :=
  let c := adjunctionPredicate a b
  namedBoth
    (.imp (.member a b) (.imp (namedPredicate a b) (.member c b)))
    (.imp (.member c b) (namedPredicate a b))

/-- Selector 8's quantified interior can be instantiated at any distinct test
name without capturing the original input or its computed witness label. -/
def adjunction_inner_instance (a b q : Nat) (hba : b ≠ a) (hbq : b ≠ q) :
    KDerivation (imp (allCode b (namedAdjunctionInner a b).encode)
      (both (imp (member a q) (imp (adjunctionPredicate a q) (member (adjunctionPredicate a b) q)))
        (imp (member (adjunctionPredicate a b) q) (adjunctionPredicate a q)))) := by
  have hc := predicate_names_lt a b
  have hbc : b ≠ adjunctionPredicate a b := by omega
  have hcb : imp (imp (equal b a) 1) (member a b) ≠ b := by
    change adjunctionPredicate a b ≠ b
    omega
  have h := CompactNamed.universalInstance b q (namedAdjunctionInner a b) hbq
    (by simp [namedAdjunctionInner, namedBoth, namedPredicate, namedEither, CompactNamed.Formula.binders])
    (by simp [namedAdjunctionInner, namedBoth, namedPredicate, namedEither, CompactNamed.Formula.binders])
  simpa [namedAdjunctionInner, namedBoth, namedPredicate, namedEither, adjunctionPredicate,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.both, CompactProof.neg, CompactDerivations.either,
    hba, hbq, hbc, hcb, Ne.symm hba, Ne.symm hbq, Ne.symm hbc] using h

/-- If the original point b denotes the input a, a selector-8 witness
contains a itself. The equality is a formula hypothesis, not name equality. -/
def adjunction_contains_input (a b : Nat) :
    KDerivation (imp (adjunctionBody a b)
      (imp (equal b a) (member (adjunctionPredicate a b) a))) := by
  let c := adjunctionPredicate a b
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal b a, adjunctionBody a b]
  have he : Context Γ (equal b a) := .hypothesis (by simp [Γ])
  have hp : Context Γ (adjunctionBody a b) := .hypothesis (by simp [Γ])
  have houter : Context Γ (imp c (member c b)) := Context.conjunctionRight hp
  have hpred : Context Γ c := .mp he (.closed (predicate_of_equal a b))
  have hmem : Context Γ (member c b) := .mp hpred houter
  exact .mp he (.mp hmem (.closed (memberRightEquality c b a)))

/-- The witness has exactly the successor membership behavior at any
capture-safe test name, provided the separate point b equals input a. -/
def adjunction_pointwise (a b q : Nat) (hba : b ≠ a) (hbq : b ≠ q) :
    KDerivation (imp (adjunctionBody a b) (imp (equal b a)
      (both (imp (member (adjunctionPredicate a b) q) (adjunctionPredicate a q))
        (imp (adjunctionPredicate a q) (member (adjunctionPredicate a b) q))))) := by
  let c := adjunctionPredicate a b
  let P := adjunctionPredicate a q
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal b a, adjunctionBody a b]
  have he : Context Γ (equal b a) := .hypothesis (by simp [Γ])
  have hp : Context Γ (adjunctionBody a b) := .hypothesis (by simp [Γ])
  have hbound : Context Γ (allCode b (namedAdjunctionInner a b).encode) := by
    have hh := Context.conjunctionLeft hp
    simpa [adjunctionBody, adjunctionPredicate, namedAdjunctionInner, namedBoth, namedPredicate, namedEither,
      CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using hh
  have hinst := Context.mp hbound (.closed (adjunction_inner_instance a b q hba hbq))
  have hforward : Context Γ (imp (member c q) P) := Context.conjunctionRight hinst
  have hpositive : Context Γ (imp (member a q) (imp P (member c q))) := Context.conjunctionLeft hinst
  have hma : Context Γ (member c a) := .mp he (.mp hp (.closed (adjunction_contains_input a b)))
  have hreverse : Context Γ (imp P (member c q)) := by
    apply Context.deduction
    have hP : Context (P :: Γ) P := Context.head Γ P
    apply Context.disjunctionElim hP
    · have heq : Context (equal q a :: P :: Γ) (equal q a) := Context.head _ _
      have hma' : Context (equal q a :: P :: Γ) (member c a) :=
        Context.under (Context.under hma P) (equal q a)
      exact .mp (Context.eqSymm heq) (.mp hma' (.closed (memberRightEquality c a q)))
    · have hm : Context (member a q :: P :: Γ) (member a q) := Context.head _ _
      have hP' : Context (member a q :: P :: Γ) P := Context.under (Context.head Γ P) (member a q)
      exact .mp hP' (.mp hm (Context.under (Context.under hpositive P) (member a q)))
  exact Context.conjunctionIntro hforward hreverse

def namedAdjunctionBody (a b : Nat) : CompactNamed.Formula :=
  let c := adjunctionPredicate a b
  namedBoth (.all b (namedAdjunctionInner a b)) (.imp (namedPredicate a b) (.member c b))

/-- With a fresh graph test name q, the exact selector-8 body plus the
explicit point/input equality yields the full successor graph for its witness. -/
def adjunction_body_successor (a b q : Nat)
    (hba : b ≠ a) (hqb : q ≠ b) (hqa : q ≠ a) (hqc : q ≠ adjunctionPredicate a b) :
    KDerivation (imp (adjunctionBody a b)
      (imp (equal b a) (successorCode a (adjunctionPredicate a b) q))) := by
  let c := adjunctionPredicate a b
  let Γ := [equal b a, adjunctionBody a b]
  have he : Context Γ (equal b a) := .hypothesis (by simp [Γ])
  have hp : Context Γ (adjunctionBody a b) := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (both (imp (member c q) (adjunctionPredicate a q))
      (imp (adjunctionPredicate a q) (member c q))) :=
    .mp he (.mp hp (.closed (adjunction_pointwise a b q hba (Ne.symm hqb))))
  let f := namedAdjunctionBody a b
  have hnames : q ∉ f.names := by
    simp [f, namedAdjunctionBody, namedAdjunctionInner, namedBoth, namedPredicate, namedEither,
      CompactNamed.Formula.names, hqb, hqa, hqc]
  have hvBody : KDerivation (imp (adjunctionBody a b) (allCode q (adjunctionBody a b))) := by
    have h := f.vacuity q hnames
    simpa [f, namedAdjunctionBody, namedAdjunctionInner, namedBoth, namedPredicate, namedEither,
      adjunctionBody, adjunctionPredicate, CompactNamed.Formula.encode,
      CompactProof.both, CompactProof.neg, CompactDerivations.either] using h
  have hvEq : KDerivation (imp (equal b a) (allCode q (equal b a))) :=
    equalityVacuity b a q hqb hqa
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode q h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases heq : h = equal b a
    · subst h
      exact hvEq
    · have hh' : h = adjunctionBody a b := hh.resolve_left heq
      subst h
      exact hvBody
  have hgraph : Context Γ (successorCode a c q) := by
    have h := Context.generalize q hv hpoint
    simpa [successorCode, adjunctionPredicate, CompactDerivations.either] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hgraph

theorem adjunction_body_successor_certificate (a b q : Nat)
    (hba : b ≠ a) (hqb : q ≠ b) (hqa : q ≠ a) (hqc : q ≠ adjunctionPredicate a b) :
    theoremCode (certificate (adjunction_body_successor a b q hba hqb hqa hqc)) =
      imp (adjunctionBody a b) (imp (equal b a) (successorCode a (adjunctionPredicate a b) q)) :=
  certificate_correct (adjunction_body_successor a b q hba hqb hqa hqc)

/-- Capture-safe introduction of an existential with a distinct variable
witness, constructed by contraposing universal instantiation. -/
def exists_variable_intro (d c : Nat) (f : CompactNamed.Formula) (hdc : d ≠ c)
    (hd : d ∉ f.binders) (hc : c ∉ f.binders) :
    KDerivation (imp (CompactNamed.replace d c f).encode (existsCode d f.encode)) := by
  have hu := CompactNamed.universalInstance d c f.not hdc
    (by simpa [CompactNamed.Formula.not, CompactNamed.Formula.binders] using hd)
    (by simpa [CompactNamed.Formula.not, CompactNamed.Formula.binders] using hc)
  have hu' : KDerivation (imp (allCode d (neg f.encode))
      (neg (CompactNamed.replace d c f).encode)) := by
    simpa [CompactNamed.Formula.not, CompactNamed.Formula.encode, CompactNamed.replace,
      CompactProof.neg] using hu
  exact compose (doubleNegIntro _) (contrapose hu')

/-- Literal named presentation of the successor graph. -/
def namedSuccessor (a d q : Nat) : CompactNamed.Formula :=
  .all q (namedSuccessorBody a d q)

/-- A concrete witness variable can be introduced into an existential
successor graph by a capture-safe variable instantiation. -/
def successor_existential_intro (a c d q : Nat)
    (hcd : c ≠ d) (hda : d ≠ a) (hcq : c ≠ q) (hdq : d ≠ q) :
    KDerivation (imp (successorCode a c q) (existsCode d (successorCode a d q))) := by
  let f := namedSuccessor a d q
  have h := exists_variable_intro d c f (Ne.symm hcd)
    (by simp [f, namedSuccessor, namedSuccessorBody, namedBoth, namedEither, CompactNamed.Formula.binders, hdq])
    (by simp [f, namedSuccessor, namedSuccessorBody, namedBoth, namedEither, CompactNamed.Formula.binders, hcq])
  simpa [f, namedSuccessor, namedSuccessorBody, namedBoth, namedEither, successorCode,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.both, CompactProof.neg, CompactDerivations.either,
    hcd, hda, hcq, hdq, Ne.symm hcd, Ne.symm hda, Ne.symm hcq, Ne.symm hdq] using h

/-- Selector 8 yields an actual existential successor-graph theorem once the
input, point, graph test, and output binder names satisfy the displayed
capture-avoidance constraints. -/
def successor_graph_exists_fresh (a b q d : Nat)
    (hba : b ≠ a) (hqb : q ≠ b) (hqa : q ≠ a) (hqc : q ≠ adjunctionPredicate a b)
    (hda : d ≠ a) (hdb : d ≠ b) (hdq : d ≠ q) (hdc : d ≠ adjunctionPredicate a b) :
    KDerivation (existsCode d (successorCode a d q)) := by
  let c := adjunctionPredicate a b
  let E := existsCode d (successorCode a d q)
  let fE : CompactNamed.Formula := .ex d (namedSuccessor a d q)
  let fGoal : CompactNamed.Formula := .imp (.equal b a) fE
  have hc := predicate_names_lt a b
  have hca : c ≠ a := by dsimp [c]; omega
  have hcb : c ≠ b := by dsimp [c]; omega
  have hcq : c ≠ q := Ne.symm hqc
  have hcd : c ≠ d := Ne.symm hdc
  have hnamesC : c ∉ fGoal.names := by
    simp [fGoal, fE, namedSuccessor, namedSuccessorBody, namedBoth, namedEither,
      CompactNamed.Formula.names, hca, hcb, hcq, hcd]
  have hvC : KDerivation (imp (imp (equal b a) E) (allCode c (imp (equal b a) E))) := by
    have h := fGoal.vacuity c hnamesC
    simpa [fGoal, fE, E, namedSuccessor, namedSuccessorBody, namedBoth, namedEither,
      successorCode, CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg,
      CompactDerivations.either] using h
  have hbody : KDerivation (imp (adjunctionBody a b) (imp (equal b a) E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [equal b a, adjunctionBody a b]
    have he : Context Γ (equal b a) := .hypothesis (by simp [Γ])
    have hp : Context Γ (adjunctionBody a b) := .hypothesis (by simp [Γ])
    have hs : Context Γ (successorCode a c q) :=
      .mp he (.mp hp (.closed (adjunction_body_successor a b q hba hqb hqa hqc)))
    exact .mp hs (.closed (successor_existential_intro a c d q hcd hda hcq hdq))
  have hcond : KDerivation (imp (equal b a) E) := by
    apply Context.closeEmpty
    apply Context.existsElim hvC
    · exact .closed (.generalize c hbody)
    · exact .closed (selector8_adjunction_witness a b)
  have hnamesB : b ∉ fE.names := by
    simp [fE, namedSuccessor, namedSuccessorBody, namedBoth, namedEither,
      CompactNamed.Formula.names, hba, Ne.symm hdb, Ne.symm hqb]
  have hvB : KDerivation (imp E (allCode b E)) := by
    have h := fE.vacuity b hnamesB
    simpa [fE, E, namedSuccessor, namedSuccessorBody, namedBoth, namedEither,
      successorCode, CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg,
      CompactDerivations.either] using h
  apply Context.closeEmpty
  apply Context.existsElim hvB
  · exact .closed (.generalize b hcond)
  · exact .closed (existsEqual b a)

/-- For every input variable, choose all auxiliary names explicitly above the
predicate code; the exact K calculus then proves a successor-graph witness. -/
def successor_graph_exists (a : Nat) :
    let b := a+1
    let c := adjunctionPredicate a b
    let q := c+1
    let d := q+1
    KDerivation (existsCode d (successorCode a d q)) := by
  dsimp only
  let b := a+1
  let c := adjunctionPredicate a b
  let q := c+1
  let d := q+1
  have hc := predicate_names_lt a b
  have hba : b ≠ a := by dsimp [b]; omega
  have hqb : q ≠ b := by dsimp [q,c]; omega
  have hqa : q ≠ a := by dsimp [q,c]; omega
  have hqc : q ≠ adjunctionPredicate a b := by dsimp [q,c]; omega
  have hda : d ≠ a := by dsimp [d,q,c]; omega
  have hdb : d ≠ b := by dsimp [d,q,c]; omega
  have hdq : d ≠ q := by dsimp [d,q]; omega
  have hdc : d ≠ adjunctionPredicate a b := by dsimp [d,q,c]; omega
  exact successor_graph_exists_fresh a b q d hba hqb hqa hqc hda hdb hdq hdc

theorem successor_graph_exists_certificate (a : Nat) :
    let b := a+1
    let c := adjunctionPredicate a b
    let q := c+1
    let d := q+1
    theoremCode (certificate (successor_graph_exists a)) = existsCode d (successorCode a d q) :=
  certificate_correct (successor_graph_exists a)

end PASoundness.PAtoCompactAdjunction
