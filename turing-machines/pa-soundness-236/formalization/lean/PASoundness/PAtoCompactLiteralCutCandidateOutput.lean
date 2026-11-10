import PASoundness.PAtoCompactLiteralCutStepFromPoint
import PASoundness.PAtoCompactLiteralCutUniformBase
import PASoundness.PAtoCompactAdditionInductionCandidateBridge

/-! The reviewed zero base and candidate induction turn an explicit K point
step into candidate-guarded output existence retaining the first input as the
literal addition cut. The point proof remains an explicit argument. This
module does not assert unconditional totality, multiplication, or PA soundness. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutCandidateOutput
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactLiteralCutAdditionDefinition (literalCut predicate)
open PASoundness.PAtoCompactLiteralCutRestrictedInduction (instance_syntax)
open PASoundness.PAtoCompactLiteralCutStepFromPoint (pointCode induction_from_point_and_base)
open PASoundness.PAtoCompactLiteralCutUniformBase (uniform_base)
open PASoundness.PAtoCompactAdditionInductionCandidateBridge (induction_candidate_bridge)
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The candidate labels may denote the same object. The premise `hpoint`
is an actual finite K proof, and no such proof is constructed here. -/
def candidate_output_from_point (hpoint : KDerivation pointCode) : KDerivation
    (imp (domainAt 100 200).encode
      (imp (domainAt 100 30).encode
        (existsCode 32 (both (domainAt 100 32).encode
          (replace 31 200 literalCut).encode)))) := by
  have hp := compose induction_candidate_bridge (induction_from_point_and_base hpoint uniform_base)
  rw [instance_syntax] at hp
  simpa [Formula.encode, andF, Formula.not, both, neg] using hp

theorem candidate_output_from_point_certificate (hpoint : KDerivation pointCode) :
    theoremCode (certificate (candidate_output_from_point hpoint)) =
      imp (domainAt 100 200).encode
        (imp (domainAt 100 30).encode
          (existsCode 32 (both (domainAt 100 32).encode
            (replace 31 200 literalCut).encode))) :=
  certificate_correct (candidate_output_from_point hpoint)
end PASoundness.PAtoCompactLiteralCutCandidateOutput
#print axioms PASoundness.PAtoCompactLiteralCutCandidateOutput.candidate_output_from_point
#print axioms PASoundness.PAtoCompactLiteralCutCandidateOutput.candidate_output_from_point_certificate
