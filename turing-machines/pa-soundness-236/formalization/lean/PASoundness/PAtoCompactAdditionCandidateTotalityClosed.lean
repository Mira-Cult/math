import PASoundness.PAtoCompactAdditionRestrictedInductionFromPoint
import PASoundness.PAtoCompactAdditionInductionPointClosed
import PASoundness.PAtoCompactAdditionInductionCandidateBridge

/-! Candidate-guarded totality for the proposed addition relation at fixed
labels. This constructs finite K proof data from the pointwise successor proof,
restricted candidate induction and the uniform zero base. It does not establish
addition functionality, general term-graph totality, PA soundness, or the
machine equivalence. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionCandidateTotalityClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactAdditionCandidateInductionInstance (predicate instance_syntax)
open PASoundness.PAtoCompactAdditionInductionPointClosed (point_closed)
open PASoundness.PAtoCompactAdditionInductionCandidateBridge (induction_candidate_bridge)
open PASoundness.PAtoCompactAdditionRestrictedInductionFromPoint (addition_from_point)
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Given candidate inputs at labels 200 and 30, some candidate output at 32
satisfies the literal proposed addition relation, with second summand 200.
No finite K proof is required as a parameter. -/
def candidate_addition_total : KDerivation
    (imp (domainAt 100 200).encode
      (imp (domainAt 100 30).encode
        (existsCode 32 (both (domainAt 100 32).encode
          (replace 31 200 additionFormula).encode)))) := by
  have hp := compose induction_candidate_bridge (addition_from_point point_closed)
  rw [instance_syntax] at hp
  simpa [Formula.encode, andF, Formula.not, both, neg] using hp

theorem candidate_addition_total_certificate :
    theoremCode (certificate candidate_addition_total) =
      imp (domainAt 100 200).encode
        (imp (domainAt 100 30).encode
          (existsCode 32 (both (domainAt 100 32).encode
            (replace 31 200 additionFormula).encode))) :=
  certificate_correct candidate_addition_total
end PASoundness.PAtoCompactAdditionCandidateTotalityClosed
#print axioms PASoundness.PAtoCompactAdditionCandidateTotalityClosed.candidate_addition_total
#print axioms PASoundness.PAtoCompactAdditionCandidateTotalityClosed.candidate_addition_total_certificate
