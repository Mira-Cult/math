import PASoundness.PAtoCompactPartialCompositionBase
import PASoundness.PAtoCompactKuratowskiAnyNames
import PASoundness.PAtoCompactPointAdjoin
import PASoundness.PAtoCompactTransitiveWitness

/-! Pair and graph witness elimination for one inside-source partial
composition step. A finite K proof of the next invariant under the supplied
pair and adjunction remains an explicit proof-data argument. This module does
not prove that step, select a composed image, or establish graph collection. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionPairElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactPartialCompositionBase PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactKuratowskiAnyNames PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Next-prefix invariant with the original graph name. -/
def nextInvariant : Formula := replace 10 13 partialComposition

/-- Next-prefix invariant with new graph name 17. -/
def nextInvariant17 : Formula := replace 9 17 nextInvariant

/-- Construct the supplied pair and point-adjoined graph, eliminate both,
then alpha-rename the resulting graph existential back to binder 9. -/
def eliminate_pair_and_graph (U : Formula)
    (h17U : 17 ∉ U.names) (h16U : 16 ∉ U.names)
    (step : KDerivation (imp U.encode (imp (pairFormula 16 10 12).encode
      (imp (adjoinCode 9 16 17 18) nextInvariant17.encode)))) :
    KDerivation (imp U.encode (existsCode 9 nextInvariant.encode)) := by
  let P := (pairFormula 16 10 12).encode
  let G := adjoinCode 9 16 17 18
  let Q := nextInvariant17.encode
  let E := existsCode 17 Q
  have hpair : KDerivation (existsCode 16 P) :=
    pair_exists_with_names 10 12 16 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hc := PASoundness.PAtoCompactPointAdjoinSelector.predicate_names_lt 9 16 23
  have h18c : 18 ≠ PASoundness.PAtoCompactPointAdjoinSelector.adjoinPredicate 9 16 23 := by omega
  have h17c : 17 ≠ PASoundness.PAtoCompactPointAdjoinSelector.adjoinPredicate 9 16 23 := by omega
  have hgraph : KDerivation (existsCode 17 G) :=
    adjoin_graph_exists_fresh 9 16 23 18 17 (by decide) (by decide)
      (by decide) (by decide) (by decide) h18c (by decide)
      (by decide) (by decide) (by decide) h17c
  have hUnderU : KDerivation (imp U.encode (imp P E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [P,U.encode]
    have hp : Context Γ P := Context.head _ _
    have hu : Context Γ U.encode := .hypothesis (by simp [Γ])
    have hlocal : Context Γ (imp G Q) := .mp hp (.mp hu (.closed step))
    have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 17 q)) := by
      intro q hq
      simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
      by_cases he : q = P
      · subst q
        exact (pairFormula 16 10 12).vacuity 17 (by decide)
      · have he' : q = U.encode := hq.resolve_left he
        subst q
        exact U.vacuity 17 h17U
    have hall : Context Γ (allCode 17 (imp G Q)) := Context.generalize 17 hv hlocal
    exact exists_map_context hall (.closed hgraph)
  have h16E : KDerivation (imp E (allCode 16 E)) := by
    let f := Formula.ex 17 nextInvariant17
    have hf : 16 ∉ f.names := by decide
    exact f.vacuity 16 hf
  have hUE : KDerivation (imp U.encode E) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [U.encode]
    have hu : Context Γ U.encode := Context.head [] _
    have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 16 q)) := by
      intro q hq
      have he : q = U.encode := by simpa [Γ] using hq
      subst q
      exact U.vacuity 16 h16U
    have hlocal : Context Γ (imp P E) := .mp hu (.closed hUnderU)
    have hall : Context Γ (allCode 16 (imp P E)) := Context.generalize 16 hv hlocal
    exact Context.existsElim h16E hall (.closed hpair)
  have halpha := (CompactNamed.existentialAlpha 9 17 nextInvariant
    (by decide) (by decide) (by decide)).2
  exact compose hUE halpha

theorem eliminate_pair_and_graph_certificate (U : Formula)
    (h17U : 17 ∉ U.names) (h16U : 16 ∉ U.names)
    (step : KDerivation (imp U.encode (imp (pairFormula 16 10 12).encode
      (imp (adjoinCode 9 16 17 18) nextInvariant17.encode)))) :
    theoremCode (certificate (eliminate_pair_and_graph U h17U h16U step)) =
      imp U.encode (existsCode 9 nextInvariant.encode) :=
  certificate_correct (eliminate_pair_and_graph U h17U h16U step)

end PASoundness.PAtoCompactPartialCompositionPairElim

#print axioms PASoundness.PAtoCompactPartialCompositionPairElim.eliminate_pair_and_graph
#print axioms PASoundness.PAtoCompactPartialCompositionPairElim.eliminate_pair_and_graph_certificate
