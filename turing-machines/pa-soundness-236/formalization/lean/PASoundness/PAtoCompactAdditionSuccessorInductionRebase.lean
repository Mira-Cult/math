import PASoundness.PAtoCompactAdditionSuccessorStepClosed

/-! Capture-safe reindexing of an explicit successor-step K derivation to
induction names. A generic proof transformer takes explicit finite K proof
data for the displayed original formula; a separate endpoint applies the
proved successor step. This is not addition totality, induction, or a PA
translation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorInductionRebase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactAdditionSuccessorPackage
open PASoundness.PAtoCompactAdditionSuccessorLocalStep
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Exact source formula, with both candidate guards and both raw successors. -/
def original : Formula := .imp fixedAssumptions (.imp additionFormula addition45)

/-- Capture-safe specialization to the induction predecessor and successor names. -/
def inductionInstance : Formula := replace 38 205 (replace 31 204 original)

/-- The specialized syntax retains distinct old/new result names and the
original two successor test binders. -/
theorem induction_instance_shape : inductionInstance =
    .imp (namedBoth (domainAt 100 204) (namedBoth (domainAt 100 32)
      (namedBoth (namedSuccessor 204 205 39) (namedSuccessor 32 45 39))))
      (.imp (replace 31 204 additionFormula)
        (replace 32 45 (replace 31 205 additionFormula))) := by
  decide

/-- A finite K proof of the original successor implication specializes to
this exact induction instance; no hypothesis about candidate existence is
inserted or discharged. -/
def rebase (h : KDerivation original.encode) : KDerivation inductionInstance.encode := by
  have h1 : KDerivation (replace 31 204 original).encode :=
    .mp (.generalize 31 h) (universalInstance 31 204 original (by decide) (by decide) (by decide))
  exact .mp (.generalize 38 h1)
    (universalInstance 38 205 (replace 31 204 original) (by decide) (by decide) (by decide))

/-- Apply the proved local successor step at the induction names. -/
def successor_step_at_induction : KDerivation inductionInstance.encode := by
  apply rebase
  change KDerivation (imp fixedAssumptions.encode (imp additionFormula.encode addition45.encode))
  exact PASoundness.PAtoCompactAdditionSuccessorStepClosed.addition_successor_step

theorem successor_step_at_induction_certificate :
    theoremCode (certificate successor_step_at_induction) = inductionInstance.encode :=
  certificate_correct successor_step_at_induction

theorem rebase_certificate (h : KDerivation original.encode) :
    theoremCode (certificate (rebase h)) = inductionInstance.encode := certificate_correct (rebase h)
end PASoundness.PAtoCompactAdditionSuccessorInductionRebase
#print axioms PASoundness.PAtoCompactAdditionSuccessorInductionRebase.induction_instance_shape
#print axioms PASoundness.PAtoCompactAdditionSuccessorInductionRebase.rebase
#print axioms PASoundness.PAtoCompactAdditionSuccessorInductionRebase.rebase_certificate

#print axioms PASoundness.PAtoCompactAdditionSuccessorInductionRebase.successor_step_at_induction
#print axioms PASoundness.PAtoCompactAdditionSuccessorInductionRebase.successor_step_at_induction_certificate
