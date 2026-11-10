import PASoundness.PAtoCompactCompositionSelectedImages
import PASoundness.PAtoCompactPartialCompositionBase
import PASoundness.PAtoCompactZeroSuccessor

/-! Scoped elimination of selected middle and target images from a supplied
fixed-old-graph composition successor proof. This module retains both actual
bijections and does not construct the input step, eliminate the old graph, or
establish an induction theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionSelectedElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactCompositionSelectedImages PASoundness.PAtoCompactPartialCompositionBase
open PASoundness.PAtoCompactConditionalTransitivityEdgeForward
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Next-prefix invariant, retaining the canonical graph name. -/
def nextInvariant : Formula := replace 10 13 partialComposition

/-- Existential output formula, with its graph bound. -/
def nextExists : Formula := .ex 9 nextInvariant

/-- Literal conclusion after eliminating the chosen middle/output witnesses. -/
def resultBody : Formula := .imp (namedSuccessor 10 13 15)
  (.imp partialComposition nextExists)

/-- The exact selected-witness fixed-graph step needed by the wrapper. -/
def selectedStepCode : Nat := imp firstImageBody.encode (imp secondImageBody.encode
  (imp (successorCode 10 13 15) (imp partialComposition.encode nextExists.encode)))

/-- Eliminate selected image witnesses using the actual two supplied
bijections and old-prefix membership. The input is explicit K proof data for
 the fixed-witness successor step; no uniform choice is assumed. -/
def eliminate_selected (step : KDerivation selectedStepCode) : KDerivation
    (imp bijectionFormula.encode (imp secondBijection.encode
      (imp (successorCode 10 13 15) (imp (member 0 10)
        (imp partialComposition.encode nextExists.encode))))) := by
  let F := firstImageBody.encode
  let S := secondImageBody.encode
  let B := both F S
  let T := resultBody.encode
  have hbody : KDerivation (imp B T) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [partialComposition.encode,successorCode 10 13 15,B]
    have hp : Context Γ partialComposition.encode := Context.head _ _
    have hs : Context Γ (successorCode 10 13 15) := .hypothesis (by simp [Γ])
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have hf : Context Γ F := Context.conjunctionLeft hb
    have hsecond : Context Γ S := Context.conjunctionRight hb
    exact .mp hp (.mp hs (.mp hsecond (.mp hf (.closed step))))
  have h12 : KDerivation (imp (existsCode 12 B) T) := by
    apply Context.closeEmpty
    apply Context.deduction
    have he : Context [existsCode 12 B] (existsCode 12 B) := Context.head [] _
    have hv : KDerivation (imp T (allCode 12 T)) := resultBody.vacuity 12 (by decide)
    exact Context.existsElim hv (.closed (.generalize 12 hbody)) he
  have h11 : KDerivation (imp selected.encode T) := by
    apply Context.closeEmpty
    apply Context.deduction
    have he : Context [selected.encode] selected.encode := Context.head [] _
    have hv : KDerivation (imp T (allCode 11 T)) := resultBody.vacuity 11 (by decide)
    exact Context.existsElim hv (.closed (.generalize 11 h12)) he
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [partialComposition.encode,member 0 10,successorCode 10 13 15,
    secondBijection.encode,bijectionFormula.encode]
  have hp : Context Γ partialComposition.encode := Context.head _ _
  have hm : Context Γ (member 0 10) := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode 10 13 15) := .hypothesis (by simp [Γ])
  have hb2 : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hb1 : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have he : Context Γ selected.encode :=
    .mp hm (.mp hb2 (.mp hb1 (.closed selected_images_exist)))
  exact .mp hp (.mp hs (.mp he (.closed h11)))

theorem eliminate_selected_certificate (step : KDerivation selectedStepCode) :
    theoremCode (certificate (eliminate_selected step)) =
      imp bijectionFormula.encode (imp secondBijection.encode
        (imp (successorCode 10 13 15) (imp (member 0 10)
          (imp partialComposition.encode nextExists.encode)))) :=
  certificate_correct (eliminate_selected step)

end PASoundness.PAtoCompactPartialCompositionSelectedElim

#print axioms PASoundness.PAtoCompactPartialCompositionSelectedElim.eliminate_selected
#print axioms PASoundness.PAtoCompactPartialCompositionSelectedElim.eliminate_selected_certificate
