import PASoundness.PAtoCompactPartialCompositionSelectionConditional
import PASoundness.PAtoCompactConditionalTransitivitySelection

/-! Assemble the exact graph-selection family under a source-candidate guard,
conditional on an explicitly supplied literal K strong-step derivation. The
candidate and both graph assumptions remain in the formal proof; this module
does not establish that the step is derivable. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionSelectionFamily
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactConditionalTransitivityPoint PASoundness.PAtoCompactConditionalTransitivityMatrix
open PASoundness.PAtoCompactConditionalTransitivitySelection
open PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactPartialCompositionInductionCompose
open PASoundness.PAtoCompactPartialCompositionSelectionConditional
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The fixed graph-name form of the exact selection clause. -/
def directBody : Formula := sourceMatrix.imp (secondMatrix.imp (.ex 9 composition))

/-- Candidate 0 uses neither graph-variable name. -/
theorem candidate_graph_fresh : 6 ∉ (namedCandidate 0).names ∧ 7 ∉ (namedCandidate 0).names := by decide

/-- Prove the selection clause for all graphs 6 and 7, retaining the candidate
hypothesis and the supplied K strong-step derivation. -/
def direct_family_of_step
    (step : KDerivation (imp bijectionFormula.encode (imp secondBijection.encode globalStep))) :
    KDerivation (imp (namedCandidate 0).encode (allCode 6 (allCode 7 directBody.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let C := (namedCandidate 0).encode
  let Γ := [C]
  have hc : Context Γ C := Context.head [] C
  have hp : Context Γ directBody.encode := by
    apply Context.deduction
    apply Context.deduction
    let Δ := [secondMatrix.encode,sourceMatrix.encode,C]
    have hm₂ : Context Δ secondMatrix.encode := Context.head _ _
    have hm₁ : Context Δ sourceMatrix.encode := .hypothesis (by simp [Δ])
    have hc' : Context Δ C := .hypothesis (by simp [Δ])
    have hb₁ : Context Δ bijectionFormula.encode := Context.conjunctionLeft hm₁
    have hb₂ : Context Δ secondBijection.encode := Context.conjunctionLeft hm₂
    exact .mp hc' (.mp hb₂ (.mp hb₁ (.closed (selection_of_step step))))
  have hv7 : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 7 q)) := by
    intro q hq
    have he : q = C := by simpa [Γ] using hq
    subst q
    exact (namedCandidate 0).vacuity 7 candidate_graph_fresh.2
  have hv6 : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 6 q)) := by
    intro q hq
    have he : q = C := by simpa [Γ] using hq
    subst q
    exact (namedCandidate 0).vacuity 6 candidate_graph_fresh.1
  exact Context.generalize 6 hv6 (Context.generalize 7 hv7 hp)

/-- Alpha-align the fixed graph names to the selection condition's 40/41
binders. Both K implications are constructed by capture-safe renaming. -/
def direct_to_selection : KDerivation
    (imp (allCode 6 (allCode 7 directBody.encode)) graphSelection.encode) := by
  let body40 := replace 6 40 directBody
  have h₁ := (universalAlpha 6 40 (.all 7 directBody) (by decide) (by decide) (by decide)).1
  have he₁ : replace 6 40 (.all 7 directBody) = .all 7 body40 := by decide
  rw [he₁] at h₁
  have h₂ := (universalAlpha 7 41 body40 (by decide) (by decide) (by decide)).1
  have he₂ : .all 40 (.all 41 (replace 7 41 body40)) = graphSelection := by decide
  have hh := compose h₁ (allCongr 40 h₂)
  change KDerivation (imp (allCode 6 (allCode 7 directBody.encode))
    (Formula.all 40 (Formula.all 41 (replace 7 41 body40))).encode) at hh
  rw [he₂] at hh
  exact hh

/-- The candidate-source hypothesis entails the exact selection condition,
conditional on the explicit K strong-step proof. -/
def selection_family_of_step
    (step : KDerivation (imp bijectionFormula.encode (imp secondBijection.encode globalStep))) :
    KDerivation (imp (namedCandidate 0).encode graphSelection.encode) :=
  compose (direct_family_of_step step) direct_to_selection

theorem selection_family_of_step_certificate
    (step : KDerivation (imp bijectionFormula.encode (imp secondBijection.encode globalStep))) :
    theoremCode (certificate (selection_family_of_step step)) =
      imp (namedCandidate 0).encode graphSelection.encode :=
  certificate_correct (selection_family_of_step step)

end PASoundness.PAtoCompactPartialCompositionSelectionFamily

#print axioms PASoundness.PAtoCompactPartialCompositionSelectionFamily.selection_family_of_step
#print axioms PASoundness.PAtoCompactPartialCompositionSelectionFamily.selection_family_of_step_certificate
