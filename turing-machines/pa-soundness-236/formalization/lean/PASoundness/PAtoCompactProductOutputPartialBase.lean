import PASoundness.PAtoCompactProductOutputImageRelation
import PASoundness.PAtoCompactMultiplicationSingleTripleExtension
import PASoundness.PAtoCompactProductMatchPartialBase

/-! Zero-prefix/zero-graph base for collecting transported product triples.
The invariant compares only guarded factor and target endpoints. No nonempty
induction step or target product graph is asserted. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputPartialBase

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactZeroExistence PASoundness.PAtoCompactZeroTransitive
open PASoundness.PAtoCompactPartialInverseBase PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactMultiplicationSingleTripleExtension PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactProductOutputImagePoint PASoundness.PAtoCompactUniformBase

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def partialBody : Formula := namedBoth (.member 59 32) pairedBody
def partialPath : Formula := .ex 32 partialBody
def bodyAt : Formula := replace 33 60 (replace 31 57 (replace 30 56 partialBody))
def pathAt : Formula := replace 33 60 (replace 31 57 (replace 30 56 partialPath))
def targetTriple : Formula := tripleAt 58 56 57 60
def endpointGuard : Formula := namedBoth (.member 43 56)
  (namedBoth (.member 44 57) (.member 42 60))
def partialInvariant : Formula := .all 56 (.all 57 (.all 60
  (.imp endpointGuard (namedBoth (.imp targetTriple pathAt) (.imp pathAt targetTriple)))))

theorem path_at_shape : pathAt = .ex 32 bodyAt := by decide
theorem body_at_shape : bodyAt = namedBoth (.member 59 32)
    (replace 33 60 (replace 31 57 (replace 30 56 pairedBody))) := by decide

def zero_prefix_excludes_path : KDerivation (imp (zeroCode 59 61) (imp pathAt.encode 1)) := by
  have hpoint : KDerivation (imp (zeroCode 59 61) (imp bodyAt.encode 1)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [bodyAt.encode,zeroCode 59 61]
    have hp : Context Γ bodyAt.encode := .head _ _
    have hz : Context Γ (zeroCode 59 61) := .hypothesis (by simp [Γ])
    have hp' : Context Γ (both (member 59 32)
        (replace 33 60 (replace 31 57 (replace 30 56 pairedBody))).encode) := by
      simpa [body_at_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hp
    have hn := Context.mp hz (.closed (zero_excludes 59 61 32 (by decide) (by decide)))
    simpa [Γ] using Context.mp (Context.conjunctionLeft hp') hn
  have h := guarded_exists_left 32 (zeroCode 59 61) bodyAt.encode 1
    (zero_graph_vacuity 59 61 32 (by decide) (by decide))
    (explosion (allCode 32 1)) hpoint
  simpa [path_at_shape, Formula.encode] using h

def tripleBody : Formula := namedBoth (pairFormula 18 56 57) (graphFormula 58 18 60)
theorem target_triple_shape : targetTriple = .ex 18 tripleBody := by decide

def zero_graph_excludes_triple : KDerivation (imp (zeroCode 58 62) (imp targetTriple.encode 1)) := by
  have hpoint : KDerivation (imp (zeroCode 58 62) (imp tripleBody.encode 1)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [tripleBody.encode,zeroCode 58 62]
    have ht : Context Γ tripleBody.encode := .head _ _
    have hz : Context Γ (zeroCode 58 62) := .hypothesis (by simp [Γ])
    have ht' : Context Γ (both (pairFormula 18 56 57).encode (graphFormula 58 18 60).encode) := by
      simpa [tripleBody, namedBoth, Formula.not, Formula.encode, both, neg] using ht
    have hn := Context.mp hz (.closed (zero_has_no_edge 58 62 18 60 (by decide) (by decide) (by decide)))
    simpa [Γ] using Context.mp (Context.conjunctionRight ht') hn
  have h := guarded_exists_left 18 (zeroCode 58 62) tripleBody.encode 1
    (zero_graph_vacuity 58 62 18 (by decide) (by decide))
    (explosion (allCode 18 1)) hpoint
  simpa [target_triple_shape, Formula.encode] using h

/-- Zero prefix and zero graph satisfy the exact guarded triple invariant. -/
def empty_prefix_empty_graph : KDerivation
    (imp (zeroCode 59 61) (imp (zeroCode 58 62) partialInvariant.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let ZP := zeroCode 59 61
  let ZH := zeroCode 58 62
  let Γ := [ZH,ZP]
  have hp : Context Γ ZP := .hypothesis (by simp [Γ])
  have hh : Context Γ ZH := .head _ _
  have hnP : Context Γ (imp pathAt.encode 1) := .mp hp (.closed zero_prefix_excludes_path)
  have hnT : Context Γ (imp targetTriple.encode 1) := .mp hh (.closed zero_graph_excludes_triple)
  have hf : Context Γ (imp targetTriple.encode pathAt.encode) := by
    apply Context.deduction
    exact Context.explode pathAt.encode (.mp (Context.head _ _) (Context.under hnT _))
  have hb : Context Γ (imp pathAt.encode targetTriple.encode) := by
    apply Context.deduction
    exact Context.explode targetTriple.encode (.mp (Context.head _ _) (Context.under hnP _))
  have hpoint : Context Γ (imp endpointGuard.encode
      (both (imp targetTriple.encode pathAt.encode) (imp pathAt.encode targetTriple.encode))) :=
    Context.lift (Context.conjunctionIntro hf hb) endpointGuard.encode
  have hv (v : Nat) (hvP : v ≠ 59) (hvP' : v ≠ 61) (hvH : v ≠ 58) (hvH' : v ≠ 62) :
      ∀ q, q ∈ Γ → KDerivation (imp q (allCode v q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases he : q = ZH
    · subst q; exact zero_graph_vacuity 58 62 v hvH hvH'
    · have he' : q = ZP := hq.resolve_left he
      subst q; exact zero_graph_vacuity 59 61 v hvP hvP'
  have hall := Context.generalize 56 (hv 56 (by decide) (by decide) (by decide) (by decide))
    (Context.generalize 57 (hv 57 (by decide) (by decide) (by decide) (by decide))
      (Context.generalize 60 (hv 60 (by decide) (by decide) (by decide) (by decide)) hpoint))
  simpa [Γ, ZH, ZP, partialInvariant, namedBoth, CompactNamed.Formula.not,
    CompactNamed.Formula.encode, both, neg] using hall

def empty_graph_exists : KDerivation (existsCode 58 (zeroCode 58 62)) := by
  let f : Formula := .all 62 (.imp (.member 1 62) .bottom)
  have ha := (existentialAlpha 1 58 f (by decide) (by decide) (by decide)).1
  have he : KDerivation (imp (existsCode 1 (zeroCode 1 62))
      (existsCode 58 (zeroCode 58 62))) := by
    simpa [f, zeroCode, neg, Formula.encode, replace, rename] using ha
  exact .mp (zero_graph_exists 62 (by decide)) he

def empty_prefix_partial_exists : KDerivation
    (imp (zeroCode 59 61) (existsCode 58 partialInvariant.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Z := zeroCode 59 61
  let Γ := [Z]
  have hz : Context Γ Z := .head _ _
  have hi : Context Γ (imp (zeroCode 58 62) partialInvariant.encode) :=
    .mp hz (.closed empty_prefix_empty_graph)
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 58 q)) := by
    intro q hq
    have he : q = Z := by simpa [Γ] using hq
    subst q
    exact zero_graph_vacuity 59 61 58 (by decide) (by decide)
  exact exists_map_context (Context.generalize 58 hv hi) (.closed empty_graph_exists)

def original : Formula := .ex 58 partialInvariant
def predicate : Formula := replace 59 64 original
theorem induction_name_fresh : 64 ∉ original.names := by decide
theorem predicate_roundtrip : replace 64 59 predicate = original :=
  replace_roundtrip 59 64 original induction_name_fresh

def empty_instance : KDerivation
    (imp (zeroCode 59 61) (replace 64 59 predicate).encode) := by
  rw [predicate_roundtrip]
  exact empty_prefix_partial_exists

def exact_uniform_base : KDerivation (uniformBaseCode 64 59 61 predicate) := by
  have h := KDerivation.generalize 59 empty_instance
  simpa [uniformBaseCode] using h

theorem exact_uniform_base_certificate : theoremCode (certificate exact_uniform_base) =
    uniformBaseCode 64 59 61 predicate := certificate_correct _

end PASoundness.PAtoCompactProductOutputPartialBase

#print axioms PASoundness.PAtoCompactProductOutputPartialBase.empty_prefix_empty_graph
#print axioms PASoundness.PAtoCompactProductOutputPartialBase.empty_prefix_partial_exists
#print axioms PASoundness.PAtoCompactProductOutputPartialBase.exact_uniform_base
#print axioms PASoundness.PAtoCompactProductOutputPartialBase.exact_uniform_base_certificate
