import PASoundness.PAtoCompactAdditionInductionCandidateAlign
import PASoundness.PAtoCompactLiteralCutInductionWitnessBind
import PASoundness.PAtoCompactUniformStep

/-! Candidate-guarded point step for the literal-cut addition-output predicate.
A concrete finite K successor law is an explicit input. Candidate alignment
and result-successor existence are proved by imported proof constructors.
This conditional module does not assert the global schema or totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutInductionPointStep
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactUniformStep PASoundness.PAtoCompactLiteralCutAdditionDefinition
open PASoundness.PAtoCompactAdditionInductionCandidateAlign
open PASoundness.PAtoCompactLiteralCutInductionWitnessBind
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private theorem previous_shape : replace 31 204 predicate =
    .imp (domainAt 100 30) (.ex 32 oldOutput) := by decide
private theorem next_shape : replace 31 205 predicate =
    .imp (domainAt 100 30) result := by decide

/-- The predecessor candidate and predecessor core lift the guarded output
predicate at 204 to the one at 205. The only proof-data input is the displayed
pointwise successor law on the two actual addition graphs. -/
def guarded_point
    (hstep : KDerivation (imp (domainAt 100 204).encode
      (imp (domainAt 100 32).encode
        (imp (successorCode 204 205 208) (imp (successorCode 32 45 39)
          (imp oldAdd.encode newAdd.encode)))))) :
    KDerivation (imp (candidateCode 204 230 209 210 232 31 203 231 206)
      (imp (predecessorCore 201 204 205 208 209 210)
        (imp (replace 31 204 predicate).encode (replace 31 205 predicate).encode))) := by
  rw [previous_shape, next_shape]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let C := candidateCode 204 230 209 210 232 31 203 231 206
  let P := predecessorCore 201 204 205 208 209 210
  let G := (domainAt 100 30).encode
  let B := imp G (existsCode 32 oldOutput.encode)
  let Γ := [G,B,P,C]
  have hg : Context Γ G := .head _ _
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hd : Context Γ (domainAt 100 204).encode := .mp hc (.closed predecessor_guard_align)
  have hs : Context Γ (successorCode 204 205 208) :=
    Context.conjunctionLeft (Context.conjunctionRight hp)
  have ho : Context Γ (existsCode 32 oldOutput.encode) := .mp hg hb
  exact .mp ho (.mp hs (.mp hd (.closed (witness_bind hstep))))

theorem guarded_point_certificate
    (hstep : KDerivation (imp (domainAt 100 204).encode
      (imp (domainAt 100 32).encode
        (imp (successorCode 204 205 208) (imp (successorCode 32 45 39)
          (imp oldAdd.encode newAdd.encode)))))) :
    theoremCode (certificate (guarded_point hstep)) =
      imp (candidateCode 204 230 209 210 232 31 203 231 206)
        (imp (predecessorCore 201 204 205 208 209 210)
          (imp (replace 31 204 predicate).encode (replace 31 205 predicate).encode)) :=
  certificate_correct (guarded_point hstep)
end PASoundness.PAtoCompactLiteralCutInductionPointStep
#print axioms PASoundness.PAtoCompactLiteralCutInductionPointStep.guarded_point
#print axioms PASoundness.PAtoCompactLiteralCutInductionPointStep.guarded_point_certificate
