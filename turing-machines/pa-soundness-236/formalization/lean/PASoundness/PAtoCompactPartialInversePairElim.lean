import PASoundness.PAtoCompactPartialInverseBase
import PASoundness.PAtoCompactKuratowskiAnyNames
import PASoundness.PAtoCompactPointAdjoin
import PASoundness.PAtoCompactTransitiveWitness

/-! Scoped pair and graph witness elimination for the inside-source partial
inverse step. The input K proof must explicitly derive the next invariant
from a supplied pair and adjunction. This module does not prove that step,
choose an image, identify the prefix alias, or establish induction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInversePairElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactPartialInverseBase PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactKuratowskiAnyNames PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact next-prefix invariant, still using graph name 7. -/
def nextInvariant : Formula := replace 8 10 partialInverse

/-- The same next invariant with the new graph name 9. -/
def nextInvariant9 : Formula := replace 7 9 nextInvariant

/-- Construct a pair and adjoined graph, eliminate them under explicit
freshness, and return the graph existential with its canonical binder 7. -/
def eliminate_pair_and_graph (U : Formula)
    (h9U : 9 ∉ U.names) (h11U : 11 ∉ U.names)
    (step : KDerivation (imp U.encode (imp (pairFormula 11 13 12).encode
      (imp (adjoinCode 7 11 9 14) nextInvariant9.encode)))) :
    KDerivation (imp U.encode (existsCode 7 nextInvariant.encode)) := by
  let P := (pairFormula 11 13 12).encode
  let G := adjoinCode 7 11 9 14
  let Q := nextInvariant9.encode
  let E := existsCode 9 Q
  have hpair : KDerivation (existsCode 11 P) :=
    pair_exists_with_names 13 12 11 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hc := PASoundness.PAtoCompactPointAdjoinSelector.predicate_names_lt 7 11 16
  have h14c : 14 ≠ PASoundness.PAtoCompactPointAdjoinSelector.adjoinPredicate 7 11 16 := by omega
  have h9c : 9 ≠ PASoundness.PAtoCompactPointAdjoinSelector.adjoinPredicate 7 11 16 := by omega
  have hgraph : KDerivation (existsCode 9 G) :=
    adjoin_graph_exists_fresh 7 11 16 14 9 (by decide) (by decide)
      (by decide) (by decide) (by decide) h14c (by decide)
      (by decide) (by decide) (by decide) h9c
  have hUnderU : KDerivation (imp U.encode (imp P E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [P,U.encode]
    have hp : Context Γ P := Context.head _ _
    have hu : Context Γ U.encode := .hypothesis (by simp [Γ])
    have hlocal : Context Γ (imp G Q) := .mp hp (.mp hu (.closed step))
    have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 9 q)) := by
      intro q hq
      simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
      by_cases he : q = P
      · subst q
        exact (pairFormula 11 13 12).vacuity 9 (by decide)
      · have he' : q = U.encode := hq.resolve_left he
        subst q
        exact U.vacuity 9 h9U
    have hall : Context Γ (allCode 9 (imp G Q)) := Context.generalize 9 hv hlocal
    exact exists_map_context hall (.closed hgraph)
  have h11E : KDerivation (imp E (allCode 11 E)) := by
    let f := Formula.ex 9 nextInvariant9
    have hf : 11 ∉ f.names := by decide
    exact f.vacuity 11 hf
  have hUE : KDerivation (imp U.encode E) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [U.encode]
    have hu : Context Γ U.encode := Context.head [] _
    have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 11 q)) := by
      intro q hq
      have he : q = U.encode := by simpa [Γ] using hq
      subst q
      exact U.vacuity 11 h11U
    have hlocal : Context Γ (imp P E) := .mp hu (.closed hUnderU)
    have hall : Context Γ (allCode 11 (imp P E)) := Context.generalize 11 hv hlocal
    exact Context.existsElim h11E hall (.closed hpair)
  have halpha := (CompactNamed.existentialAlpha 7 9 nextInvariant
    (by decide) (by decide) (by decide)).2
  exact compose hUE halpha

theorem eliminate_pair_and_graph_certificate (U : Formula)
    (h9U : 9 ∉ U.names) (h11U : 11 ∉ U.names)
    (step : KDerivation (imp U.encode (imp (pairFormula 11 13 12).encode
      (imp (adjoinCode 7 11 9 14) nextInvariant9.encode)))) :
    theoremCode (certificate (eliminate_pair_and_graph U h9U h11U step)) =
      imp U.encode (existsCode 7 nextInvariant.encode) :=
  certificate_correct (eliminate_pair_and_graph U h9U h11U step)

end PASoundness.PAtoCompactPartialInversePairElim

#print axioms PASoundness.PAtoCompactPartialInversePairElim.eliminate_pair_and_graph
#print axioms PASoundness.PAtoCompactPartialInversePairElim.eliminate_pair_and_graph_certificate
