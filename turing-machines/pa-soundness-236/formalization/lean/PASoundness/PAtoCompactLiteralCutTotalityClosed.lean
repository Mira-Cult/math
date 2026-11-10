import PASoundness.PAtoCompactLiteralCutCandidateOutput
import PASoundness.PAtoCompactLiteralCutInductionPointStep
import PASoundness.PAtoCompactLiteralCutSuccessorInductionRebase

/-! Candidate-guarded addition-output existence with the first input as a
literal cut. The proof composes finite K data for the zero base, exact
successor step, and candidate-restricted induction. This is a fixed-name
result, not an arbitrary-name interface, multiplication totality, or the PA
soundness bridge. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutTotalityClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactLiteralCutAdditionDefinition (literalCut predicate)
open PASoundness.PAtoCompactLiteralCutStepFromPoint (pointCode)
open PASoundness.PAtoCompactLiteralCutCandidateOutput (candidate_output_from_point)
open PASoundness.PAtoCompactLiteralCutInductionPointStep (guarded_point)
open PASoundness.PAtoCompactLiteralCutSuccessorInductionRebase (local_successor)
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The exact point proof, with the candidate at 205 retained as a literal
antecedent even though the constructed step does not need it. -/
def point_closed : KDerivation pointCode := by
  let C := candidateCode 204 230 209 210 232 31 203 231 206
  let D := candidateCode 205 234 209 210 237 31 240 231 206
  let P := predecessorCore 201 204 205 208 209 210
  let F := (replace 31 204 predicate).encode
  let Γ := [F,P,D,C]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hf : Context Γ F := .head _ _
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  exact .mp hf (.mp hp (.mp hc (.closed (guarded_point local_successor))))

/-- Given candidate inputs at labels 200 and 30, K constructs a candidate
output at 32 whose cut is literally the first input. The two input labels may
represent the same object; no proof-data input is required. -/
def candidate_literal_cut_total : KDerivation
    (imp (domainAt 100 200).encode
      (imp (domainAt 100 30).encode
        (existsCode 32 (both (domainAt 100 32).encode
          (replace 31 200 literalCut).encode)))) :=
  candidate_output_from_point point_closed

theorem candidate_literal_cut_total_certificate :
    theoremCode (certificate candidate_literal_cut_total) =
      imp (domainAt 100 200).encode
        (imp (domainAt 100 30).encode
          (existsCode 32 (both (domainAt 100 32).encode
            (replace 31 200 literalCut).encode))) :=
  certificate_correct candidate_literal_cut_total
end PASoundness.PAtoCompactLiteralCutTotalityClosed
#print axioms PASoundness.PAtoCompactLiteralCutTotalityClosed.point_closed
#print axioms PASoundness.PAtoCompactLiteralCutTotalityClosed.candidate_literal_cut_total
#print axioms PASoundness.PAtoCompactLiteralCutTotalityClosed.candidate_literal_cut_total_certificate
