import PASoundness.PAtoCompactProductMatchRelation
import PASoundness.PAtoCompactPartialCompositionBase
import PASoundness.PAtoCompactUniformBase

/-! Empty-prefix base for a represented partial product-match graph. The
match relation is the concrete pointwise path formula; no global graph
collection, successor step, or product congruence is asserted here. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchPartialBase

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactZeroExistence
open PASoundness.PAtoCompactZeroTransitive PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPartialInverseBase
open PASoundness.PAtoCompactProductMatchRelation PASoundness.PAtoCompactUniformBase

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The concrete source/target match with source name 56 and target name 57. -/
def matchAt : Formula := replace 35 57 (replace 32 56 path)

/-- Graph 58 realizes the match relation on source-prefix 59, for source
members of 2 and target members of 44. The graph may contain unrelated edges
outside these guarded endpoints; the exact claim is this displayed invariant. -/
def partialMatch : Formula := .all 56 (.all 57
  (.imp (namedBoth (.member 2 56) (.member 44 57))
    (namedBoth (.imp (graphFormula 58 56 57) (namedBoth (.member 59 56) matchAt))
      (.imp (namedBoth (.member 59 56) matchAt) (graphFormula 58 56 57)))))

/-- A zero prefix and a zero graph satisfy the literal partial-match
invariant. No product or factor-bijection assumption is used in the base. -/
def empty_prefix_empty_graph : KDerivation
    (imp (zeroCode 59 60) (imp (zeroCode 58 61) partialMatch.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let ZP := zeroCode 59 60
  let ZH := zeroCode 58 61
  let E := (graphFormula 58 56 57).encode
  let P := both (member 59 56) matchAt.encode
  let Y := both (member 2 56) (member 44 57)
  let Γ := [ZH,ZP]
  have hp : Context Γ ZP := .hypothesis (by simp [Γ])
  have hh : Context Γ ZH := .head _ _
  have hnp : Context Γ (neg (member 59 56)) :=
    .mp hp (.closed (zero_excludes 59 60 56 (by decide) (by decide)))
  have hng : Context Γ (neg E) :=
    .mp hh (.closed (zero_has_no_edge 58 61 56 57 (by decide) (by decide) (by decide)))
  have hf : Context Γ (imp E P) := by
    apply Context.deduction
    exact Context.explode P (.mp (Context.head _ E) (Context.under hng E))
  have hb : Context Γ (imp P E) := by
    apply Context.deduction
    let Δ := [P,ZH,ZP]
    have ht : Context Δ P := .head _ _
    have hm : Context Δ (member 59 56) := Context.conjunctionLeft ht
    exact Context.explode E (.mp hm (Context.under hnp P))
  have hpoint : Context Γ (imp Y (both (imp E P) (imp P E))) :=
    Context.lift (Context.conjunctionIntro hf hb) Y
  have hv57 : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 57 q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = ZH
    · subst q; exact zero_graph_vacuity 58 61 57 (by decide) (by decide)
    · have he' : q = ZP := hq.resolve_left he
      subst q; exact zero_graph_vacuity 59 60 57 (by decide) (by decide)
  have hv56 : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 56 q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = ZH
    · subst q; exact zero_graph_vacuity 58 61 56 (by decide) (by decide)
    · have he' : q = ZP := hq.resolve_left he
      subst q; exact zero_graph_vacuity 59 60 56 (by decide) (by decide)
  have h := Context.generalize 56 hv56 (Context.generalize 57 hv57 hpoint)
  simpa [partialMatch, namedBoth, Formula.not, Formula.encode, both, neg, E, P, Y] using h

/-- Selector 8 constructs an empty graph at the designated graph name. -/
def empty_graph_exists : KDerivation (existsCode 58 (zeroCode 58 61)) := by
  let f : Formula := .all 61 (.imp (.member 1 61) .bottom)
  have ha := (existentialAlpha 1 58 f (by decide) (by decide) (by decide)).1
  have he : KDerivation (imp (existsCode 1 (zeroCode 1 61))
      (existsCode 58 (zeroCode 58 61))) := by
    simpa [f, zeroCode, neg, Formula.encode, replace, rename] using ha
  exact .mp (zero_graph_exists 61 (by decide)) he

/-- Every zero prefix has a represented partial-match graph. -/
def empty_prefix_partial_exists : KDerivation
    (imp (zeroCode 59 60) (existsCode 58 partialMatch.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Z := zeroCode 59 60
  let Γ := [Z]
  have hz : Context Γ Z := .head _ _
  have hi : Context Γ (imp (zeroCode 58 61) partialMatch.encode) :=
    .mp hz (.closed empty_prefix_empty_graph)
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 58 q)) := by
    intro q hq
    have he : q = Z := by simpa [Γ] using hq
    subst q
    exact zero_graph_vacuity 59 60 58 (by decide) (by decide)
  exact exists_map_context (Context.generalize 58 hv hi) (.closed empty_graph_exists)

def original : Formula := .ex 58 partialMatch
def predicate : Formula := replace 59 64 original

theorem induction_name_fresh : 64 ∉ original.names := by decide

theorem predicate_roundtrip : replace 64 59 predicate = original :=
  replace_roundtrip 59 64 original induction_name_fresh

def empty_instance : KDerivation
    (imp (zeroCode 59 60) (replace 64 59 predicate).encode) := by
  rw [predicate_roundtrip]
  exact empty_prefix_partial_exists

/-- Uniform zero base for candidate induction with prefix name 64. -/
def exact_uniform_base : KDerivation (uniformBaseCode 64 59 60 predicate) := by
  have h := KDerivation.generalize 59 empty_instance
  simpa [uniformBaseCode] using h

theorem empty_prefix_partial_exists_certificate :
    theoremCode (certificate empty_prefix_partial_exists) =
      imp (zeroCode 59 60) (existsCode 58 partialMatch.encode) := certificate_correct _

theorem exact_uniform_base_certificate : theoremCode (certificate exact_uniform_base) =
    uniformBaseCode 64 59 60 predicate := certificate_correct _

end PASoundness.PAtoCompactProductMatchPartialBase

#print axioms PASoundness.PAtoCompactProductMatchPartialBase.empty_prefix_empty_graph
#print axioms PASoundness.PAtoCompactProductMatchPartialBase.empty_graph_exists
#print axioms PASoundness.PAtoCompactProductMatchPartialBase.empty_prefix_partial_exists
#print axioms PASoundness.PAtoCompactProductMatchPartialBase.exact_uniform_base
#print axioms PASoundness.PAtoCompactProductMatchPartialBase.empty_prefix_partial_exists_certificate
#print axioms PASoundness.PAtoCompactProductMatchPartialBase.exact_uniform_base_certificate
