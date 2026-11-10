import PASoundness.PAtoCompactSeededSpanStep
import PASoundness.PAtoCompactKuratowskiAnyNames
import PASoundness.PAtoCompactTransitiveWitness

/-! Construct and eliminate the pair and adjoined-graph witnesses for one
seeded common-source span successor. The old invariant, both selected image bodies,
common-input membership and successor prefix remain explicit K antecedents.
This does not yet select images from the input clauses, eliminate the old graph
or prove candidate induction. -/
namespace PASoundness.PAtoCompactSeededSpanStepWitness

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactKuratowskiAnyNames
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveWitness PASoundness.PAtoCompactCommonSourceSpanBase
open PASoundness.PAtoCompactCommonSourceSpanImages PASoundness.PAtoCompactSeededSpanStep
open PASoundness.PAtoCompactSeededSpanBase

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Retained old graph, both selected images with uniqueness, common-source
membership and the actual prefix-successor relation. -/
def retained : Formula := namedBoth seededSpan
  (namedBoth firstImageBody (namedBoth secondImageBody
    (namedBoth (.member 1 10) (namedSuccessor 10 13 15))))

theorem retained_fresh_16 : 16 ∉ retained.names := by decide
theorem retained_fresh_17 : 17 ∉ retained.names := by decide

/-- The next span invariant renamed to use graph name 9 as its binder. -/
def nextInvariant : Formula := replace 17 9 nextSpan

theorem next_rename_alignment : replace 9 17 nextInvariant = nextSpan := by decide

/-- Retain the selected hypotheses when supplying a pair and adjoined graph. -/
def curried_step : KDerivation (imp retained.encode
    (imp (pairFormula 16 11 12).encode
      (imp (adjoinCode 9 16 17 18) nextSpan.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [adjoinCode 9 16 17 18,(pairFormula 16 11 12).encode,retained.encode]
  have ha : Context Γ (adjoinCode 9 16 17 18) := .head _ _
  have hp : Context Γ (pairFormula 16 11 12).encode := .hypothesis (by simp [Γ])
  have hr : Context Γ retained.encode := .hypothesis (by simp [Γ])
  have hi := Context.conjunctionLeft hr
  have hrest := Context.conjunctionRight hr
  have hf := Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hs := Context.conjunctionLeft hrest
  have hrest := Context.conjunctionRight hrest
  have hm := Context.conjunctionLeft hrest
  have hsucc := Context.conjunctionRight hrest
  have hguard : Context Γ stepGuard.encode := Context.conjunctionIntro hi
    (Context.conjunctionIntro hf (Context.conjunctionIntro hs (Context.conjunctionIntro hm
      (Context.conjunctionIntro hsucc (Context.conjunctionIntro hp ha)))))
  exact .mp hguard (.closed supplied_span_successor)

/-- K constructs and eliminates the ordered pair and adjoined graph, retaining
the selected-image and old-prefix hypotheses. -/
def next_graph_exists : KDerivation (imp retained.encode (existsCode 9 nextInvariant.encode)) := by
  let P := (pairFormula 16 11 12).encode
  let G := adjoinCode 9 16 17 18
  let Q := nextSpan.encode
  let E := existsCode 17 Q
  have hpair : KDerivation (existsCode 16 P) :=
    pair_exists_with_names 11 12 16 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hc := PASoundness.PAtoCompactPointAdjoinSelector.predicate_names_lt 9 16 23
  have h18c : 18 ≠ PASoundness.PAtoCompactPointAdjoinSelector.adjoinPredicate 9 16 23 := by omega
  have h17c : 17 ≠ PASoundness.PAtoCompactPointAdjoinSelector.adjoinPredicate 9 16 23 := by omega
  have hgraph : KDerivation (existsCode 17 G) :=
    adjoin_graph_exists_fresh 9 16 23 18 17 (by decide) (by decide)
      (by decide) (by decide) (by decide) h18c (by decide)
      (by decide) (by decide) (by decide) h17c
  have hUnderU : KDerivation (imp retained.encode (imp P E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [P,retained.encode]
    have hp : Context Γ P := .head _ _
    have hu : Context Γ retained.encode := .hypothesis (by simp [Γ])
    have hlocal : Context Γ (imp G Q) := .mp hp (.mp hu (.closed curried_step))
    have hv : ∀ x, x ∈ Γ → KDerivation (imp x (allCode 17 x)) := by
      intro x hx
      simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hx
      by_cases he : x = P
      · subst x; exact (pairFormula 16 11 12).vacuity 17 (by decide)
      · have he' : x = retained.encode := hx.resolve_left he
        subst x; exact retained.vacuity 17 retained_fresh_17
    have hall := Context.generalize 17 hv hlocal
    exact exists_map_context hall (.closed hgraph)
  have h16E : KDerivation (imp E (allCode 16 E)) := by
    let f := Formula.ex 17 nextSpan
    have hf : 16 ∉ f.names := by decide
    exact f.vacuity 16 hf
  have hUE : KDerivation (imp retained.encode E) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [retained.encode]
    have hu : Context Γ retained.encode := .head _ _
    have hv : ∀ x, x ∈ Γ → KDerivation (imp x (allCode 16 x)) := by
      intro x hx
      have he : x = retained.encode := by simpa [Γ] using hx
      subst x
      exact retained.vacuity 16 retained_fresh_16
    have hlocal : Context Γ (imp P E) := .mp hu (.closed hUnderU)
    have hall := Context.generalize 16 hv hlocal
    exact Context.existsElim h16E hall (.closed hpair)
  have halpha := (existentialAlpha 9 17 nextInvariant
    (by decide) (by decide) (by decide)).2
  rw [next_rename_alignment] at halpha
  exact compose hUE halpha

theorem next_graph_exists_certificate : theoremCode (certificate next_graph_exists) =
    imp retained.encode (existsCode 9 nextInvariant.encode) := certificate_correct next_graph_exists

end PASoundness.PAtoCompactSeededSpanStepWitness

#print axioms PASoundness.PAtoCompactSeededSpanStepWitness.retained
#print axioms PASoundness.PAtoCompactSeededSpanStepWitness.retained_fresh_16
#print axioms PASoundness.PAtoCompactSeededSpanStepWitness.retained_fresh_17
#print axioms PASoundness.PAtoCompactSeededSpanStepWitness.nextInvariant
#print axioms PASoundness.PAtoCompactSeededSpanStepWitness.next_rename_alignment
#print axioms PASoundness.PAtoCompactSeededSpanStepWitness.curried_step
#print axioms PASoundness.PAtoCompactSeededSpanStepWitness.next_graph_exists
#print axioms PASoundness.PAtoCompactSeededSpanStepWitness.next_graph_exists_certificate
