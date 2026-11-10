import PASoundness.PAtoCompactPartialInverseInsideClosed
import PASoundness.PAtoCompactPartialInverseGuardedGlobalStep

/-! Exact composition of both source-membership branches into the strong
global step for the partial-inverse predicate. The original graph's actual
bijection remains an object-level antecedent. This is not induction or a
proof that an inverse graph exists for the full source. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseGlobalStepClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPartialInverseBase PASoundness.PAtoCompactPartialInversePredicate
open PASoundness.PAtoCompactPartialInverseOutsidePredicate PASoundness.PAtoCompactPartialInverseInsideClosed
open PASoundness.PAtoCompactPartialInverseGuardedGlobalStep PASoundness.PAtoCompactQuantifiedRefutation

/-- The inside-source extension has exactly the induction predicate's two
literal prefix instances, with the graph witnesses existentially eliminated. -/
def inside_predicate_step : KDerivation
    (imp bijectionFormula.encode (imp (successorCode 8 10 15)
      (imp (member 0 8)
        (imp (replace 30 8 predicate).encode (replace 30 10 predicate).encode)))) := by
  rw [instance_roundtrip, successor_instance]
  exact inside_successor_closed

/-- The actual forward-bijection formula yields the exact strong global
successor schema for the partial-inverse predicate. No source-membership
case or witness remains as a metatheoretic premise. -/
def guarded_global_step : KDerivation
    (imp bijectionFormula.encode
      (allCode 31 (allStepsCode 31 30 8 10 15 32 33 predicate))) :=
  guarded_global_step_of_inside inside_predicate_step

theorem guarded_global_step_certificate :
    theoremCode (certificate guarded_global_step) =
      imp bijectionFormula.encode
        (allCode 31 (allStepsCode 31 30 8 10 15 32 33 predicate)) :=
  certificate_correct guarded_global_step

end PASoundness.PAtoCompactPartialInverseGlobalStepClosed

#print axioms PASoundness.PAtoCompactPartialInverseGlobalStepClosed.inside_predicate_step
#print axioms PASoundness.PAtoCompactPartialInverseGlobalStepClosed.guarded_global_step
#print axioms PASoundness.PAtoCompactPartialInverseGlobalStepClosed.guarded_global_step_certificate
