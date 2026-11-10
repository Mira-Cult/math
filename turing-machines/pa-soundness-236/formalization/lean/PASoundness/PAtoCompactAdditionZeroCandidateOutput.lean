import PASoundness.PAtoCompactAdditionRightZeroWitness
import PASoundness.PAtoCompactCandidateBinderBridge
import PASoundness.PAtoCompactGuardBaseTransport
import PASoundness.PAtoCompactVacuousUniversal
import PASoundness.PAtoCompactAdjunction

/-! A candidate-guarded output witness in the fixed right-zero addition case.
Both the displayed input candidate and the right-input zero graph remain
premises; this does not prove arbitrary addition existence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionZeroCandidateOutput

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactAdditionRightZeroWitness PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactCandidateFieldTransport PASoundness.PAtoCompactCandidateBinderBridge
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactVacuousUniversal

/-- Relocate the eight private binders of the fixed input candidate to the
independent canonical block used to guard the output. -/
def input_candidate_to_guard : KDerivation
    (imp (candidateCode 30 41 37 38 32 0 31 34 35) (domainAt 100 30).encode) := by
  have h1 := transitivity_field 30 41 37 38 32 0 31 34 35 133 134 (by decide)
  have h2 := member_field 30 41 133 134 32 0 31 34 35 132 (by decide)
  have h3 := subset_field 30 132 133 134 32 0 31 34 35 135 (by decide) (by decide)
  have h4 := subset_test_field 30 132 133 134 135 0 31 34 35 136 (by decide) (by decide)
  have h5 := nonempty_field 30 132 133 134 135 136 31 34 35 137 (by decide)
  have h6 := witness_field 30 132 133 134 135 136 137 34 35 138 (by decide) (by decide)
  have h7 := order_field 30 132 133 134 135 136 137 138 35 139 (by decide) (by decide)
  rw [domainAt_encode]
  exact compose h1 (compose h2 (compose h3 (compose h4 (compose h5 (compose h6 h7)))))

def outputBody : Formula := andF (domainAt 100 32) additionFormula

private theorem output_instance : replace 32 30 outputBody =
    andF (domainAt 100 30) same_output_addition := by
  simp [outputBody, andF, Formula.not, replace, replace_domainAt 100 32 30 (by decide),
    same_output_addition]

/-- K constructs an output with both the candidate guard and literal
addition relation when the right operand is the displayed zero. -/
def right_zero_candidate_output : KDerivation
    (imp (candidateCode 30 41 37 38 32 0 31 34 35)
      (imp (zeroCode 31 36) (existsCode 32 outputBody.encode))) := by
  have hi : KDerivation (imp (andF (domainAt 100 30) same_output_addition).encode
      (existsCode 32 outputBody.encode)) := by
    have h := exists_variable_intro 32 30 outputBody (by decide) (by decide) (by decide)
    rw [output_instance] at h
    exact h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [zeroCode 31 36, candidateCode 30 41 37 38 32 0 31 34 35]
  have hz : Context Γ (zeroCode 31 36) := .head _ _
  have hc : Context Γ (candidateCode 30 41 37 38 32 0 31 34 35) :=
    .hypothesis (by simp [Γ])
  have hd : Context Γ (domainAt 100 30).encode := .mp hc (.closed input_candidate_to_guard)
  have ha : Context Γ same_output_addition.encode := .mp hz (.mp hc (.closed candidate_add_zero))
  have hp : Context Γ (andF (domainAt 100 30) same_output_addition).encode := by
    simpa [andF, Formula.not, Formula.encode, both, neg] using Context.conjunctionIntro hd ha
  exact .mp hp (.closed hi)

theorem right_zero_candidate_output_certificate :
    theoremCode (certificate right_zero_candidate_output) =
      imp (candidateCode 30 41 37 38 32 0 31 34 35)
        (imp (zeroCode 31 36) (existsCode 32 outputBody.encode)) := certificate_correct _

end PASoundness.PAtoCompactAdditionZeroCandidateOutput

#print axioms PASoundness.PAtoCompactAdditionZeroCandidateOutput.input_candidate_to_guard
#print axioms PASoundness.PAtoCompactAdditionZeroCandidateOutput.right_zero_candidate_output
#print axioms PASoundness.PAtoCompactAdditionZeroCandidateOutput.right_zero_candidate_output_certificate
