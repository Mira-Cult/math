import PASoundness.PAtoCompactPartialCompositionBase
import PASoundness.PAtoCompactConditionalTransitivityEdgeForward
import PASoundness.PAtoCompactAdjunction

/-! Existential elimination of the old partial-composition graph from an
explicit supplied fixed-graph successor derivation. This wrapper neither
proves that step nor establishes induction or composition-graph existence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionOldGraphElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactPartialCompositionBase
open PASoundness.PAtoCompactConditionalTransitivityEdgeForward
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The same invariant at the new prefix, with graph name 9 still free. -/
def nextInvariant : Formula := replace 10 13 partialComposition

/-- Rename the output graph binder away from old graph name 9. -/
def nextWithBinder26 : Formula := .ex 26 (replace 9 26 nextInvariant)

/-- An explicit fixed-old-graph successor proof, retaining both bijections. -/
def oldGraphStepCode : Nat := imp bijectionFormula.encode (imp secondBijection.encode
  (imp (successorCode 10 13 15) (imp (member 0 10)
    (imp partialComposition.encode (existsCode 9 nextInvariant.encode)))))

/-- Eliminate the old graph while the output binder is explicitly renamed to
26, retaining all original hypotheses and the supplied fixed-graph proof. -/
def eliminate_old_graph_renamed (step : KDerivation oldGraphStepCode) : KDerivation
    (imp bijectionFormula.encode (imp secondBijection.encode (imp (successorCode 10 13 15)
      (imp (member 0 10) (imp (existsCode 9 partialComposition.encode) nextWithBinder26.encode))))) := by
  let B1 := bijectionFormula.encode
  let B2 := secondBijection.encode
  let S := successorCode 10 13 15
  let M := member 0 10
  let P := partialComposition.encode
  let T := nextWithBinder26.encode
  let Γ := [M,S,B2,B1]
  have hb1 : Context Γ B1 := .hypothesis (by simp [Γ])
  have hb2 : Context Γ B2 := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hm : Context Γ M := Context.head _ _
  have halpha : KDerivation (imp (existsCode 9 nextInvariant.encode) T) :=
    (existentialAlpha 9 26 nextInvariant (by decide) (by decide) (by decide)).1
  have hfixed : Context Γ (imp P (existsCode 9 nextInvariant.encode)) :=
    .mp hm (.mp hs (.mp hb2 (.mp hb1 (.closed step))))
  have hlocal : Context Γ (imp P T) := by
    apply Context.deduction
    have hp : Context (P :: Γ) P := Context.head _ _
    exact .mp (.mp hp (Context.under hfixed P)) (.closed halpha)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 9 h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases heM : h = M
    · subst h
      exact membershipVacuity 0 10 9 (by decide) (by decide)
    · by_cases heS : h = S
      · subst h
        exact (namedSuccessor 10 13 15).vacuity 9 (by decide)
      · by_cases heB2 : h = B2
        · subst h
          exact secondBijection.vacuity 9 (by decide)
        · have heB1 : h = B1 := ((hh.resolve_left heM).resolve_left heS).resolve_left heB2
          subst h
          exact bijectionFormula.vacuity 9 (by decide)
  have hall : Context Γ (allCode 9 (imp P T)) := Context.generalize 9 hv hlocal
  have htarget : KDerivation (imp T (allCode 9 T)) :=
    nextWithBinder26.vacuity 9 (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Δ := [existsCode 9 P,M,S,B2,B1]
  have he : Context Δ (existsCode 9 P) := Context.head _ _
  have hall' : Context Δ (allCode 9 (imp P T)) := Context.weaken hall (by
    intro h hh; exact List.mem_cons_of_mem _ hh)
  exact Context.existsElim htarget hall' he

/-- Return to the exact original output binder 9 after old-graph elimination. -/
def eliminate_old_graph (step : KDerivation oldGraphStepCode) : KDerivation
    (imp bijectionFormula.encode (imp secondBijection.encode (imp (successorCode 10 13 15)
      (imp (member 0 10) (imp (existsCode 9 partialComposition.encode)
        (existsCode 9 nextInvariant.encode)))))) := by
  have halpha : KDerivation (imp nextWithBinder26.encode (existsCode 9 nextInvariant.encode)) :=
    (existentialAlpha 9 26 nextInvariant (by decide) (by decide) (by decide)).2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [existsCode 9 partialComposition.encode,member 0 10,successorCode 10 13 15,
    secondBijection.encode,bijectionFormula.encode]
  have he : Context Γ (existsCode 9 partialComposition.encode) := Context.head _ _
  have hm : Context Γ (member 0 10) := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode 10 13 15) := .hypothesis (by simp [Γ])
  have hb2 : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hb1 : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have ht : Context Γ nextWithBinder26.encode :=
    .mp he (.mp hm (.mp hs (.mp hb2 (.mp hb1 (.closed (eliminate_old_graph_renamed step))))))
  exact .mp ht (.closed halpha)

theorem eliminate_old_graph_certificate (step : KDerivation oldGraphStepCode) :
    theoremCode (certificate (eliminate_old_graph step)) =
      imp bijectionFormula.encode (imp secondBijection.encode (imp (successorCode 10 13 15)
        (imp (member 0 10) (imp (existsCode 9 partialComposition.encode)
          (existsCode 9 nextInvariant.encode))))) :=
  certificate_correct (eliminate_old_graph step)

end PASoundness.PAtoCompactPartialCompositionOldGraphElim

#print axioms PASoundness.PAtoCompactPartialCompositionOldGraphElim.eliminate_old_graph
#print axioms PASoundness.PAtoCompactPartialCompositionOldGraphElim.eliminate_old_graph_certificate
