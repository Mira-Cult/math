import PASoundness.PAtoCompactQuotientLeftOrder
import PASoundness.PAtoCompactCandidateRestrictedSymmetryClosed
import PASoundness.PAtoCompactCandidateSymmetryObject

/-! Opposite orientation for left-order substitution. This uses guarded
symmetry and the separately proved one-witness order substitution. Both
literal candidate conditions remain explicit antecedents; no general quotient
interpretation or PA proof translation is claimed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotientLeftOrderReverse
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateSymmetryObject
open PASoundness.PAtoCompactCandidateRestrictedSymmetryClosed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoSwap
open PASoundness.PAtoCompactQuotientLeftOrder

/-- Capture-safe swap of the two object names in the guarded symmetry body.
Name 8 is only an intermediate in this proof of a closed implication. -/
def symmetryBody : Formula := PASoundness.PAtoCompactCandidateSymmetryObject.sourceBody

def swappedBody : Formula := replace 8 1 (replace 1 0 (replace 0 8 symmetryBody))

theorem swapped_body_syntax : swappedBody = .imp (namedSymmetryCandidate 1)
    (.imp reverseEquivalent equivalentFormula) := by decide

/-- Specialize guarded symmetry to source 1 and target 0. -/
def symmetry_at_one : KDerivation
    (imp (candidateCode 1 37 32 33 34 30 35 10 36)
      (imp reverseEquivalent.encode equivalentFormula.encode)) := by
  have h : KDerivation symmetryBody.encode := by
    simpa only [symmetryBody, PASoundness.PAtoCompactCandidateSymmetryObject.sourceBody,
      Formula.encode, named_candidate_code,
      PASoundness.PAtoCompactPartialInverseAtSource.named_candidate_code] using candidate_symmetry_closed
  have h1 := (.mp (.generalize 0 h)
    (universalInstance 0 8 symmetryBody (by decide) (by decide) (by decide)) :
      KDerivation (replace 0 8 symmetryBody).encode)
  have h2 := (.mp (.generalize 1 h1)
    (universalInstance 1 0 (replace 0 8 symmetryBody) (by decide) (by decide) (by decide)) :
      KDerivation (replace 1 0 (replace 0 8 symmetryBody)).encode)
  have h3 := (.mp (.generalize 8 h2)
    (universalInstance 8 1 (replace 1 0 (replace 0 8 symmetryBody)) (by decide) (by decide) (by decide)) :
      KDerivation swappedBody.encode)
  rw [swapped_body_syntax] at h3
  exact h3

/-- With both candidate guards, E(1,0) transports Less(1,8) to Less(0,8).
The literal Less formulas and their existential witness are unchanged. -/
def left_order_substitutivity_reverse : KDerivation
    (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp (candidateCode 1 37 32 33 34 30 35 10 36)
        (imp reverseEquivalent.encode (imp sourceLess.encode targetLess.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [sourceLess.encode, reverseEquivalent.encode,
    candidateCode 1 37 32 33 34 30 35 10 36,
    candidateCode 0 37 32 33 34 30 35 10 36]
  have h0 : Context Γ (candidateCode 0 37 32 33 34 30 35 10 36) := .hypothesis (by simp [Γ])
  have h1 : Context Γ (candidateCode 1 37 32 33 34 30 35 10 36) := .hypothesis (by simp [Γ])
  have hr : Context Γ reverseEquivalent.encode := .hypothesis (by simp [Γ])
  have hl : Context Γ sourceLess.encode := Context.head _ _
  have he : Context Γ equivalentFormula.encode := .mp hr (.mp h1 (.closed symmetry_at_one))
  exact .mp hl (.mp he (.mp h0 (.closed left_order_substitutivity)))

theorem left_order_substitutivity_reverse_certificate :
    theoremCode (certificate left_order_substitutivity_reverse) =
      imp (candidateCode 0 37 32 33 34 30 35 10 36)
        (imp (candidateCode 1 37 32 33 34 30 35 10 36)
          (imp reverseEquivalent.encode (imp sourceLess.encode targetLess.encode))) :=
  certificate_correct left_order_substitutivity_reverse

end PASoundness.PAtoCompactQuotientLeftOrderReverse

#print axioms PASoundness.PAtoCompactQuotientLeftOrderReverse.symmetry_at_one
#print axioms PASoundness.PAtoCompactQuotientLeftOrderReverse.left_order_substitutivity_reverse
#print axioms PASoundness.PAtoCompactQuotientLeftOrderReverse.left_order_substitutivity_reverse_certificate
