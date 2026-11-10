import PASoundness.PAtoCompactProductMatchInsideImage
import PASoundness.PAtoCompactKuratowskiAnyNames
import PASoundness.PAtoCompactPointAdjoin
import PASoundness.PAtoCompactTransitiveWitness

/-! Pair/new-graph witness construction for the inside-source product-match
extension. The preservation of the next invariant under that adjunction
remains an explicit K proof-data input and is not established here. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchInsideAdjoinConditional

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactKuratowskiAnyNames
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactProductMatchPartialBase PASoundness.PAtoCompactProductMatchOutsideStep
open PASoundness.PAtoCompactProductMatchInsideImage

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The selected path and old graph are retained while adjoining one edge. -/
def retained : Formula := namedBoth selectedPath
  (namedBoth (namedSuccessor 74 59 76) oldMatch)

def nextInvariant17 : Formula := replace 58 17 partialMatch

/-- Local graph-invariant obligation for an explicitly supplied Kuratowski
pair and point-adjoined graph. The selected source endpoint is 74 and its
matched target is 35. -/
def AdjoinInvariant : Type := KDerivation
  (imp retained.encode (imp (pairFormula 16 74 35).encode
    (imp (adjoinCode 58 16 17 18) nextInvariant17.encode)))

/-- Construct and eliminate the pair and point-adjoined graph. The argument
`step` is the still-open next-invariant proof, not a graph existence axiom. -/
def new_graph_of_adjoin (step : AdjoinInvariant) : KDerivation
    (imp retained.encode (existsCode 58 partialMatch.encode)) := by
  let P := (pairFormula 16 74 35).encode
  let G := adjoinCode 58 16 17 18
  let Q := nextInvariant17.encode
  let E := existsCode 17 Q
  have hpair : KDerivation (existsCode 16 P) :=
    pair_exists_with_names 74 35 16 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hc := PASoundness.PAtoCompactPointAdjoinSelector.predicate_names_lt 58 16 23
  have h18c : 18 ≠ PASoundness.PAtoCompactPointAdjoinSelector.adjoinPredicate 58 16 23 := by omega
  have h17c : 17 ≠ PASoundness.PAtoCompactPointAdjoinSelector.adjoinPredicate 58 16 23 := by omega
  have hgraph : KDerivation (existsCode 17 G) :=
    adjoin_graph_exists_fresh 58 16 23 18 17 (by decide) (by decide)
      (by decide) (by decide) (by decide) h18c (by decide)
      (by decide) (by decide) (by decide) h17c
  have hUnder : KDerivation (imp retained.encode (imp P E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [P,retained.encode]
    have hp : Context Γ P := .head _ _
    have hu : Context Γ retained.encode := .hypothesis (by simp [Γ])
    have hlocal : Context Γ (imp G Q) := .mp hp (.mp hu (.closed step))
    have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 17 q)) := by
      intro q hq
      simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
      by_cases he : q = P
      · subst q; exact (pairFormula 16 74 35).vacuity 17 (by decide)
      · have he' : q = retained.encode := hq.resolve_left he
        subst q; exact retained.vacuity 17 (by decide)
    exact exists_map_context (Context.generalize 17 hv hlocal) (.closed hgraph)
  have h16E : KDerivation (imp E (allCode 16 E)) := by
    let f := Formula.ex 17 nextInvariant17
    have hf : 16 ∉ f.names := by decide
    exact f.vacuity 16 hf
  have hUE : KDerivation (imp retained.encode E) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [retained.encode]
    have hu : Context Γ retained.encode := .head _ _
    have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 16 q)) := by
      intro q hq
      have he : q = retained.encode := by simpa [Γ] using hq
      subst q; exact retained.vacuity 16 (by decide)
    have hlocal : Context Γ (imp P E) := .mp hu (.closed hUnder)
    have hall : Context Γ (allCode 16 (imp P E)) := Context.generalize 16 hv hlocal
    exact Context.existsElim h16E hall (.closed hpair)
  have halpha := (existentialAlpha 58 17 partialMatch (by decide) (by decide) (by decide)).2
  simpa [nextInvariant17, Formula.encode] using compose hUE halpha

theorem new_graph_of_adjoin_certificate (step : AdjoinInvariant) :
    theoremCode (certificate (new_graph_of_adjoin step)) =
      imp retained.encode (existsCode 58 partialMatch.encode) := certificate_correct _

end PASoundness.PAtoCompactProductMatchInsideAdjoinConditional

#print axioms PASoundness.PAtoCompactProductMatchInsideAdjoinConditional.new_graph_of_adjoin
#print axioms PASoundness.PAtoCompactProductMatchInsideAdjoinConditional.new_graph_of_adjoin_certificate
