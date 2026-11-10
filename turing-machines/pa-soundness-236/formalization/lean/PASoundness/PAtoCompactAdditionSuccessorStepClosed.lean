import PASoundness.PAtoCompactAdditionSuccessorLocalStep
import PASoundness.PAtoCompactAdditionOldWitnessElim

/-! Literal finite-K successor step for addition. The original addition
formula and candidate/explicit successor assumptions are supplied; no global
induction, totality, PA bridge, or semantic soundness shortcut is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorStepClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactAdditionSuccessorPackage
open PASoundness.PAtoCompactAdditionSuccessorLocalStep PASoundness.PAtoCompactAdditionOldWitnessElim
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Candidate guards for the old second summand and old result, and explicit
raw successors for each, turn an old addition witness into the literal new
addition relation. This is a finite K proof, not an addition-totality theorem. -/
def addition_successor_step : KDerivation (imp fixedAssumptions.encode
    (imp additionFormula.encode addition45.encode)) := by
  apply eliminate_old_witnesses fixedAssumptions addition45
    (by decide) (by decide) (by decide) (by decide)
  exact local_step

theorem addition_successor_step_certificate : theoremCode (certificate addition_successor_step) =
    imp fixedAssumptions.encode (imp additionFormula.encode addition45.encode) :=
  certificate_correct addition_successor_step
end PASoundness.PAtoCompactAdditionSuccessorStepClosed
#print axioms PASoundness.PAtoCompactAdditionSuccessorStepClosed.addition_successor_step
#print axioms PASoundness.PAtoCompactAdditionSuccessorStepClosed.addition_successor_step_certificate
