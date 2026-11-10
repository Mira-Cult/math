import PASoundness.PAtoCompactAdditionIdentityClosedCut
import PASoundness.PAtoCompactCandidateReflexivity

/-! Literal K right-zero graph witness for the candidate object itself.
The candidate and supplied zero graph remain explicit hypotheses. This
constructs one operation instance, not totality or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionRightZeroWitness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactAdditionIdentityClosedCut PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactCandidateReflexivity PASoundness.PAtoCompactDiagonalReflexiveMatrixTransport
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Capture-safe literal addition formula with output identified with its
first operand. Name 30 is not bound inside the source addition formula. -/
def same_output_addition : Formula := replace 32 30 additionFormula
private def source : Formula := .imp (.all 36 (Formula.member 31 36).not)
  (.imp (equivAt 30 32) additionFormula)
private def target : Formula := .imp (.all 36 (Formula.member 31 36).not)
  (.imp (equivAt 30 30) same_output_addition)
private theorem source_replacement : replace 32 30 source = target := by decide
private theorem refl_syntax : equivAt 30 30 = reflexive30 := by rfl

private def specialized : KDerivation target.encode := by
  have hp : KDerivation source.encode := by
    simpa [source,Formula.encode,Formula.not,zeroCode,neg] using addition_of_zero_right
  have h := universalInstance 32 30 source (by decide) (by decide) (by decide)
  rw [source_replacement] at h
  exact .mp (.generalize 32 hp) h

/-- K proves the actual same-output addition instance under the fixed-name
candidate and explicit zero witness. -/
def candidate_add_zero : KDerivation
    (imp (candidateCode 30 41 37 38 32 0 31 34 35)
      (imp (zeroCode 31 36) same_output_addition.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [zeroCode 31 36,candidateCode 30 41 37 38 32 0 31 34 35]
  have hz : Context Γ (zeroCode 31 36) := .head _ _
  have hc : Context Γ (candidateCode 30 41 37 38 32 0 31 34 35) := .hypothesis (by simp [Γ])
  have he : Context Γ (equivAt 30 30).encode := by
    simpa [refl_syntax] using (Context.mp hc (.closed candidate_reflexive))
  have hs : Context Γ (imp (zeroCode 31 36)
      (imp (equivAt 30 30).encode same_output_addition.encode)) := by
    simpa [target,Formula.encode,Formula.not,zeroCode,neg] using (Context.closed specialized : Context Γ target.encode)
  exact .mp he (.mp hz hs)

theorem candidate_add_zero_certificate : theoremCode (certificate candidate_add_zero) =
    imp (candidateCode 30 41 37 38 32 0 31 34 35)
      (imp (zeroCode 31 36) same_output_addition.encode) :=
  certificate_correct candidate_add_zero
end PASoundness.PAtoCompactAdditionRightZeroWitness
#print axioms PASoundness.PAtoCompactAdditionRightZeroWitness.candidate_add_zero
#print axioms PASoundness.PAtoCompactAdditionRightZeroWitness.candidate_add_zero_certificate
