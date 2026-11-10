import PASoundness.PAtoCompactPartialCompositionAtSource
import PASoundness.PAtoCompactPartialCompositionFullProjection

/-! Conditional selection of a represented restricted-composition graph.
The K strong-step proof is supplied as proof data. Both input bijections and
source candidacy remain literal object-level hypotheses. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionSelectionConditional
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactConditionalTransitivityMatrix
open PASoundness.PAtoCompactPartialCompositionInductionCompose
open PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactPartialCompositionFullProjection
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A supplied global-step proof yields an actual represented restricted
composition graph under the two bijections and source-candidate hypotheses. -/
def selection_of_step
    (step : KDerivation (imp bijectionFormula.encode (imp secondBijection.encode globalStep))) :
    KDerivation (imp bijectionFormula.encode (imp secondBijection.encode
      (imp (candidateCode 0 37 32 33 34 30 35 13 36)
        (existsCode 9 PASoundness.PAtoCompactConditionalTransitivityPoint.composition.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let C := candidateCode 0 37 32 33 34 30 35 13 36
  let Γ := [C,secondBijection.encode,bijectionFormula.encode]
  have hc : Context Γ C := Context.head _ _
  have hs : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ (existsCode 9 fullPrefix.encode) :=
    .mp hc (.mp hs (.mp hf (.closed (source_composition_of_step step))))
  exact .mp hp (.closed full_prefix_exists_to_composition_exists)

theorem selection_of_step_certificate
    (step : KDerivation (imp bijectionFormula.encode (imp secondBijection.encode globalStep))) :
    theoremCode (certificate (selection_of_step step)) =
      imp bijectionFormula.encode (imp secondBijection.encode
        (imp (candidateCode 0 37 32 33 34 30 35 13 36)
          (existsCode 9 PASoundness.PAtoCompactConditionalTransitivityPoint.composition.encode))) :=
  certificate_correct (selection_of_step step)

end PASoundness.PAtoCompactPartialCompositionSelectionConditional

#print axioms PASoundness.PAtoCompactPartialCompositionSelectionConditional.selection_of_step
#print axioms PASoundness.PAtoCompactPartialCompositionSelectionConditional.selection_of_step_certificate
