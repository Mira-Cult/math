import PASoundness.PAtoCompactPartialInverseBase

/-! Partial restricted-composition graph and its zero-prefix base in literal
K. The existence proof below constructs only an empty-prefix graph. It does
not establish successor extension, arbitrary graph collection, or quotient
transitivity. Code 1 remains literal compact bottom. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionBase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactZeroExistence PASoundness.PAtoCompactZeroTransitive
open PASoundness.PAtoCompactTransitiveWitness PASoundness.PAtoCompactPartialInverseBase
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not
private def iff' (a b : Formula) : Formula := conj (a.imp b) (b.imp a)

/-- Names 0,1,8 denote source, middle and target; 6,7 are supplied graphs,
9 the partial composition graph, and 10 its source prefix. Names 2,3,4 and
graph-internal 19–22 are bound. Correspondence is asserted only on the
source/target domains, including absence of edges beyond the current prefix. -/
def partialComposition : Formula := .all 2 (.all 3
  (.imp (conj (.member 0 2) (.member 8 3))
    (iff' (graphFormula 9 2 3)
      (conj (.member 10 2) (.ex 4 (conj (.member 1 4)
        (conj (graphFormula 6 2 4) (graphFormula 7 4 3))))))))

theorem partialComposition_free : partialComposition.free = {0,1,6,7,8,9,10} := by decide

/-- A zero prefix and a zero output graph establish the exact invariant. No
assumption on the two supplied input graphs is required. -/
def empty_prefix_empty_graph : KDerivation
    (imp (zeroCode 10 11) (imp (zeroCode 9 12) partialComposition.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let ZP := zeroCode 10 11
  let ZH := zeroCode 9 12
  let G := (graphFormula 9 2 3).encode
  let O := (Formula.ex 4 (conj (.member 1 4)
    (conj (graphFormula 6 2 4) (graphFormula 7 4 3)))).encode
  let T := both (member 10 2) O
  let Y := both (member 0 2) (member 8 3)
  let Γ := [ZH,ZP]
  have hp : Context Γ ZP := .hypothesis (by simp [Γ])
  have hh : Context Γ ZH := Context.head [ZP] _
  have hnp : Context Γ (neg (member 10 2)) :=
    .mp hp (.closed (zero_excludes 10 11 2 (by decide) (by decide)))
  have hng : Context Γ (neg G) :=
    .mp hh (.closed (zero_has_no_edge 9 12 2 3 (by decide) (by decide) (by decide)))
  have hforward : Context Γ (imp G T) := by
    apply Context.deduction
    exact Context.explode T (.mp (Context.head _ G) (Context.under hng G))
  have hback : Context Γ (imp T G) := by
    apply Context.deduction
    let Δ := [T,ZH,ZP]
    have ht : Context Δ T := Context.head _ _
    have hm : Context Δ (member 10 2) := Context.conjunctionLeft ht
    exact Context.explode G (.mp hm (Context.under hnp T))
  have hpoint : Context Γ (imp Y (both (imp G T) (imp T G))) :=
    Context.lift (Context.conjunctionIntro hforward hback) Y
  have hv3 : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 3 q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = ZH
    · subst q
      exact zero_graph_vacuity 9 12 3 (by decide) (by decide)
    · have he' : q = ZP := hq.resolve_left he
      subst q
      exact zero_graph_vacuity 10 11 3 (by decide) (by decide)
  have hv2 : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 2 q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = ZH
    · subst q
      exact zero_graph_vacuity 9 12 2 (by decide) (by decide)
    · have he' : q = ZP := hq.resolve_left he
      subst q
      exact zero_graph_vacuity 10 11 2 (by decide) (by decide)
  exact Context.generalize 2 hv2 (Context.generalize 3 hv3 hpoint)

/-- Selector 8 supplies a zero graph at name 9 after alpha conversion. -/
def empty_graph_exists : KDerivation (existsCode 9 (zeroCode 9 12)) := by
  let f : Formula := .all 12 (.imp (.member 1 12) .bottom)
  have ha := (existentialAlpha 1 9 f (by decide) (by decide) (by decide)).1
  have he : KDerivation (imp (existsCode 1 (zeroCode 1 12))
      (existsCode 9 (zeroCode 9 12))) := by
    simpa [f, zeroCode, neg, Formula.encode, replace, rename] using ha
  exact .mp (zero_graph_exists 12 (by decide)) he

/-- Any zero prefix admits a represented partial composition graph. -/
def empty_prefix_partial_composition_exists : KDerivation
    (imp (zeroCode 10 11) (existsCode 9 partialComposition.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Z := zeroCode 10 11
  let Γ := [Z]
  have hz : Context Γ Z := Context.head [] _
  have hi : Context Γ (imp (zeroCode 9 12) partialComposition.encode) :=
    .mp hz (.closed empty_prefix_empty_graph)
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 9 q)) := by
    intro q hq
    have he : q = Z := by simpa [Γ] using hq
    subst q
    exact zero_graph_vacuity 10 11 9 (by decide) (by decide)
  have hall := Context.generalize 9 hv hi
  exact exists_map_context hall (.closed empty_graph_exists)

theorem empty_prefix_partial_composition_certificate :
    theoremCode (certificate empty_prefix_partial_composition_exists) =
      imp (zeroCode 10 11) (existsCode 9 partialComposition.encode) :=
  certificate_correct empty_prefix_partial_composition_exists

end PASoundness.PAtoCompactPartialCompositionBase

#print axioms PASoundness.PAtoCompactPartialCompositionBase.empty_prefix_partial_composition_exists
#print axioms PASoundness.PAtoCompactPartialCompositionBase.empty_prefix_partial_composition_certificate
