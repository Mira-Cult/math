import PASoundness.PAtoCompactSuccCongruenceData
import PASoundness.PAtoCompactGraphContextElim
import PASoundness.CompactFreshen
import PASoundness.CompactQuantifiers
import PASoundness.PAtoCompactSuccCongruencePairAlias

/-! The supplied adjoined graph has no edge except an old edge or the newly
adjoined pair. Pair-coordinate comparison is supplied as K proof data; graph
and pair witnesses remain explicit object-level hypotheses. No graph existence,
collection or successor congruence is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccCongruenceEdgeSplit
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactGraphContextElim
open PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactSuccCongruencePairAlias
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- An old edge or the endpoint pair that was added to graph 6. -/
def conclusion : Formula := namedEither (graphFormula 6 2 3)
  (namedBoth (.equal 2 0) (.equal 3 1))

theorem conclusion_code : conclusion.encode = either (graphFormula 6 2 3).encode
    (both (equal 2 0) (equal 3 1)) := rfl

/-- Point-coordinate comparison is an explicit K proof-data premise. -/
def aliasCode : Nat := imp (equal 19 11) (imp (pairFormula 19 2 3).encode
  (imp newPair (both (equal 2 0) (equal 3 1))))

private theorem conclusion_names_lt : ∀ v ∈ conclusion.names, v < 30 := by
  intro v hv
  have hm := Finset.le_sup (f := id) hv
  change v ≤ conclusion.names.sup id at hm
  have hb : conclusion.names.sup id < 30 := by decide
  omega

private def freshConclusion := freshen conclusion 30 conclusion_names_lt

/-- The target is vacuous at the outer graph witness despite internally
binding 19 in its old-graph disjunct: alpha-convert that binder first. -/
def conclusion_vacuity : KDerivation (imp conclusion.encode (allCode 19 conclusion.encode)) :=
  compose freshConclusion.equivalent.forward
    (compose (freshConclusion.formula.vacuity 19 (by decide))
      (allCongr 19 freshConclusion.equivalent.backward))

/-- Inspect the adjoined graph at the explicit graph witness. -/
def adjoin_instance : KDerivation (imp newGraph
    (imp (member 9 19) (either (member 6 19) (equal 19 11)))) := by
  let E := either (equal 19 11) (member 6 19)
  let B := both (imp (member 9 19) E) (imp E (member 9 19))
  let f : Formula := namedBoth (.imp (.member 9 16)
      (namedEither (.equal 16 11) (.member 6 16)))
    (.imp (namedEither (.equal 16 11) (.member 6 16)) (.member 9 16))
  have hi := universalInstance 16 19 f (by decide) (by decide) (by decide)
  have hi' : KDerivation (imp newGraph B) := by
    simpa [f, newGraph, adjoinCode, B, E, namedBoth, namedEither, Formula.encode,
      CompactNamed.replace, CompactNamed.rename, CompactProof.both,
      CompactProof.neg, CompactDerivations.either] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 9 19,newGraph]
  have ha : Context Γ newGraph := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 9 19) := Context.head _ _
  have hb : Context Γ B := .mp ha (.closed hi')
  have he : Context Γ E := .mp hm (Context.conjunctionLeft hb)
  apply Context.disjunctionElim he
  · exact Context.disjunctionRight (a := member 6 19) (Context.head _ _)
  · exact Context.disjunctionLeft (b := equal 19 11) (Context.head _ _)

private def oldGraphBody : Formula := match graphFormula 6 2 3 with
  | .ex _ f => f
  | _ => .truth

/-- The displayed old member and pair witness introduce the old graph edge. -/
def old_graph_intro : KDerivation
    (imp (both (member 6 19) (pairFormula 19 2 3).encode) (graphFormula 6 2 3).encode) :=
  existsIntroduce 19 oldGraphBody (by decide)

private def adjoin_vacuity : KDerivation (imp newGraph (allCode 19 newGraph)) := by
  let f := namedAdjoin 6 11 9 16
  have hv := f.vacuity 19 (by decide)
  simpa [f, namedAdjoin, newGraph, namedBoth, namedEither, Formula.encode, adjoinCode,
    CompactProof.both, CompactProof.neg, CompactDerivations.either] using hv

private def pair_vacuity : KDerivation (imp newPair (allCode 19 newPair)) :=
  (pairFormula 11 0 1).vacuity 19 (by decide)

/-- A graph edge of the supplied adjunction is old or has the appended
coordinates, conditional only on the exact supplied K pair-alias derivation. -/
def edge_split_conditional (hAlias : KDerivation aliasCode) : KDerivation
    (imp newGraph (imp newPair (imp (graphFormula 9 2 3).encode conclusion.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let P := (pairFormula 19 2 3).encode
  let B := both (member 9 19) P
  let R := both (equal 2 0) (equal 3 1)
  let G := (graphFormula 6 2 3).encode
  let Γ := [newPair,newGraph]
  have ha : Context Γ newGraph := .hypothesis (by simp [Γ])
  have hq : Context Γ newPair := Context.head _ _
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 19 h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = newPair
    · subst h; exact pair_vacuity
    · have he' : h = newGraph := hh.resolve_left he
      subst h; exact adjoin_vacuity
  have hs : Context Γ (imp B conclusion.encode) := by
    apply Context.deduction
    have hb : Context (B :: Γ) B := Context.head _ _
    have hm : Context (B :: Γ) (member 9 19) := Context.conjunctionLeft hb
    have hp : Context (B :: Γ) P := Context.conjunctionRight hb
    have ha' : Context (B :: Γ) newGraph := Context.under ha _
    have hq' : Context (B :: Γ) newPair := Context.under hq _
    have hc : Context (B :: Γ) (either (member 6 19) (equal 19 11)) :=
      .mp hm (.mp ha' (.closed adjoin_instance))
    change Context (B :: Γ) (either G R)
    apply Context.disjunctionElim hc
    · have hold : Context (member 6 19 :: B :: Γ) (member 6 19) := Context.head _ _
      have hp' : Context (member 6 19 :: B :: Γ) P := Context.under hp _
      have hg : Context (member 6 19 :: B :: Γ) G :=
        .mp (Context.conjunctionIntro hold hp') (.closed old_graph_intro)
      exact Context.disjunctionLeft (b := R) hg
    · have he : Context (equal 19 11 :: B :: Γ) (equal 19 11) := Context.head _ _
      have hp' : Context (equal 19 11 :: B :: Γ) P := Context.under hp _
      have hq'' : Context (equal 19 11 :: B :: Γ) newPair := Context.under hq' _
      have hr : Context (equal 19 11 :: B :: Γ) R := .mp hq'' (.mp hp' (.mp he (.closed hAlias)))
      exact Context.disjunctionRight (a := G) hr
  exact graph_context_imp Γ 9 2 3 conclusion hv conclusion_vacuity hs

theorem edge_split_conditional_certificate (hAlias : KDerivation aliasCode) :
    theoremCode (certificate (edge_split_conditional hAlias)) =
      imp newGraph (imp newPair (imp (graphFormula 9 2 3).encode conclusion.encode)) :=
  certificate_correct (edge_split_conditional hAlias)

/-- The actual K coordinate-alias proof discharges the proof-data premise;
the supplied adjunction and pair remain explicit formula antecedents. -/
def edge_split : KDerivation
    (imp newGraph (imp newPair (imp (graphFormula 9 2 3).encode conclusion.encode))) :=
  edge_split_conditional new_pair_alias

theorem edge_split_certificate : theoremCode (certificate edge_split) =
    imp newGraph (imp newPair (imp (graphFormula 9 2 3).encode conclusion.encode)) :=
  certificate_correct edge_split

/-- The supplied pair and adjunction imply the edge split uniformly over
both displayed edge-coordinate names. -/
def edge_split_all : KDerivation (imp newGraph (imp newPair
    (allCode 2 (allCode 3 (imp (graphFormula 9 2 3).encode conclusion.encode))))) := by
  let Γ := [newPair,newGraph]
  let P := imp (graphFormula 9 2 3).encode conclusion.encode
  have ha : Context Γ newGraph := .hypothesis (by simp [Γ])
  have hp : Context Γ newPair := Context.head _ _
  have hpoint : Context Γ P := .mp hp (.mp ha (.closed edge_split))
  have hv (k : Nat) (hkA : k ∉ (namedAdjoin 6 11 9 16).names)
      (hkP : k ∉ (pairFormula 11 0 1).names) :
      ∀ h, h ∈ Γ → KDerivation (imp h (allCode k h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = newPair
    · subst h
      exact (pairFormula 11 0 1).vacuity k hkP
    · have he' : h = newGraph := hh.resolve_left he
      subst h
      have h := (namedAdjoin 6 11 9 16).vacuity k hkA
      simpa [newGraph, namedAdjoin, namedBoth, namedEither, Formula.encode,
        adjoinCode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using h
  have h3 : Context Γ (allCode 3 P) := Context.generalize 3 (hv 3 (by decide) (by decide)) hpoint
  have h2 : Context Γ (allCode 2 (allCode 3 P)) :=
    Context.generalize 2 (hv 2 (by decide) (by decide)) h3
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact h2

theorem edge_split_all_certificate : theoremCode (certificate edge_split_all) =
    imp newGraph (imp newPair
      (allCode 2 (allCode 3 (imp (graphFormula 9 2 3).encode conclusion.encode)))) :=
  certificate_correct edge_split_all

/-- Capture-safe version with a fixed source name 2 and quantified target
name 4, for the bijection uniqueness clause. -/
def edge_split_target4 : KDerivation (imp newGraph (imp newPair
    (allCode 4 (imp (graphFormula 9 2 4).encode
      (either (graphFormula 6 2 4).encode (both (equal 2 0) (equal 4 1))))))) := by
  let body : Formula := .imp (graphFormula 9 2 3) conclusion
  let body4 : Formula := .imp (graphFormula 9 2 4)
    (namedEither (graphFormula 6 2 4) (namedBoth (.equal 2 0) (.equal 4 1)))
  have hs := allSpecialize 2 (.all 3 body) (by decide)
  have ha := (universalAlpha 3 4 body (by decide) (by decide) (by decide)).1
  have hsyntax : replace 3 4 body = body4 := by decide
  rw [hsyntax] at ha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [newPair,newGraph]
  have hp : Context Γ newPair := Context.head _ _
  have hg : Context Γ newGraph := .hypothesis (by simp [Γ])
  have hall : Context Γ (allCode 2 (allCode 3 body.encode)) :=
    .mp hp (.mp hg (.closed edge_split_all))
  have h3 : Context Γ (allCode 3 body.encode) := .mp hall (.closed hs)
  have h4 : Context Γ (allCode 4 body4.encode) := .mp h3 (.closed ha)
  exact h4

theorem edge_split_target4_certificate : theoremCode (certificate edge_split_target4) =
    imp newGraph (imp newPair (allCode 4 (imp (graphFormula 9 2 4).encode
      (either (graphFormula 6 2 4).encode (both (equal 2 0) (equal 4 1)))))) :=
  certificate_correct edge_split_target4

/-- Capture-safe point instance for the second edge in the exact order
matrix, whose source and target names are 4 and 5. -/
def edge_split_45 : KDerivation (imp newGraph (imp newPair
    (imp (graphFormula 9 4 5).encode
      (either (graphFormula 6 4 5).encode (both (equal 4 0) (equal 5 1)))))) := by
  let body : Formula := .imp (graphFormula 9 2 3) conclusion
  let body43 : Formula := .imp (graphFormula 9 4 3)
    (namedEither (graphFormula 6 4 3) (namedBoth (.equal 4 0) (.equal 3 1)))
  let body45 : Formula := .imp (graphFormula 9 4 5)
    (namedEither (graphFormula 6 4 5) (namedBoth (.equal 4 0) (.equal 5 1)))
  have h24 := universalInstance 2 4 (.all 3 body) (by decide) (by decide) (by decide)
  have h24syntax : replace 2 4 (.all 3 body) = .all 3 body43 := by decide
  rw [h24syntax] at h24
  have h35 := universalInstance 3 5 body43 (by decide) (by decide) (by decide)
  have h35syntax : replace 3 5 body43 = body45 := by decide
  rw [h35syntax] at h35
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [newPair,newGraph]
  have hp : Context Γ newPair := Context.head _ _
  have hg : Context Γ newGraph := .hypothesis (by simp [Γ])
  have hall : Context Γ (allCode 2 (allCode 3 body.encode)) :=
    .mp hp (.mp hg (.closed edge_split_all))
  have h3 : Context Γ (allCode 3 body43.encode) := .mp hall (.closed h24)
  have h5 : Context Γ body45.encode := .mp h3 (.closed h35)
  exact h5

theorem edge_split_45_certificate : theoremCode (certificate edge_split_45) =
    imp newGraph (imp newPair (imp (graphFormula 9 4 5).encode
      (either (graphFormula 6 4 5).encode (both (equal 4 0) (equal 5 1))))) :=
  certificate_correct edge_split_45

end PASoundness.PAtoCompactSuccCongruenceEdgeSplit

#print axioms PASoundness.PAtoCompactSuccCongruenceEdgeSplit.edge_split_conditional
#print axioms PASoundness.PAtoCompactSuccCongruenceEdgeSplit.edge_split_conditional_certificate
#print axioms PASoundness.PAtoCompactSuccCongruenceEdgeSplit.edge_split
#print axioms PASoundness.PAtoCompactSuccCongruenceEdgeSplit.edge_split_certificate
#print axioms PASoundness.PAtoCompactSuccCongruenceEdgeSplit.edge_split_all
#print axioms PASoundness.PAtoCompactSuccCongruenceEdgeSplit.edge_split_all_certificate
#print axioms PASoundness.PAtoCompactSuccCongruenceEdgeSplit.edge_split_target4
#print axioms PASoundness.PAtoCompactSuccCongruenceEdgeSplit.edge_split_target4_certificate
#print axioms PASoundness.PAtoCompactSuccCongruenceEdgeSplit.edge_split_45
#print axioms PASoundness.PAtoCompactSuccCongruenceEdgeSplit.edge_split_45_certificate
