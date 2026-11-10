import PASoundness.PAtoCompactFirstAdditionOperandTransport
import PASoundness.PAtoCompactAllocatedAdditionToRaw
import PASoundness.PAtoCompactScopedActiveReplace

/-! Lift the witnessed operand transport to the actual base-100 allocated
addition formula in both its input and output. -/
namespace PASoundness.PAtoCompactFirstAdditionOperandTransportAllocated

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactAdditionZeroAllocated PASoundness.PAtoCompactAddBaseInventory

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guard : Formula := namedBoth PASoundness.PAtoCompactFirstAdditionOperandTransport.fixedGuard
  (addAt 100 28 1 0)

private def frame : Formula := .imp additionFormula (addAt 100 30 31 32)
private def moved29 : Formula := replace 30 29 frame
private def moved27 : Formula := replace 31 27 moved29
private theorem template_eq : addTemplate = additionFormula := by decide

private def new_raw_to_allocated : KDerivation
    (imp PASoundness.PAtoCompactFirstAdditionOperandTransport.newAddition.encode (addAt 100 29 27 0).encode) := by
  have hbase : KDerivation frame.encode := by
    have h := original_allocated_alpha 100 (by decide)
    rw [template_eq] at h
    exact h.forward
  have h29 := replace_derivation 30 29 frame (by decide) (by decide) hbase
  have h27 := replace_derivation 31 27 moved29 (by decide) (by decide) (by simpa only [moved29] using h29)
  have h0 := replace_derivation 32 0 moved27 (by decide) (by decide) (by simpa only [moved27] using h27)
  have halign : replace 32 0 moved27 = .imp PASoundness.PAtoCompactFirstAdditionOperandTransport.newAddition
      (addAt 100 29 27 0) := by decide
  rw [halign] at h0
  exact h0

/-- Transport the old allocated addition to the new equivalent operand
pair, with the candidate and equivalence hypotheses of fixedGuard explicit. -/
def allocated_operand_transport : KDerivation (imp guard.encode (addAt 100 29 27 0).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hf : Context Γ PASoundness.PAtoCompactFirstAdditionOperandTransport.fixedGuard.encode := Context.conjunctionLeft hg
  have ha : Context Γ (addAt 100 28 1 0).encode := Context.conjunctionRight hg
  have hraw : Context Γ PASoundness.PAtoCompactFirstAdditionCutAllocation.addition.encode :=
    .mp ha (.closed PASoundness.PAtoCompactAllocatedAdditionToRaw.first_allocated_to_raw)
  have hguard : Context Γ PASoundness.PAtoCompactFirstAdditionOperandTransport.guard.encode :=
    Context.conjunctionIntro hf hraw
  have hnew : Context Γ PASoundness.PAtoCompactFirstAdditionOperandTransport.newAddition.encode :=
    .mp hguard (.closed PASoundness.PAtoCompactFirstAdditionOperandTransport.transport_first_addition_operands)
  exact .mp hnew (.closed new_raw_to_allocated)

theorem allocated_operand_transport_certificate : theoremCode (certificate allocated_operand_transport) =
    imp guard.encode (addAt 100 29 27 0).encode := certificate_correct allocated_operand_transport

end PASoundness.PAtoCompactFirstAdditionOperandTransportAllocated

#print axioms PASoundness.PAtoCompactFirstAdditionOperandTransportAllocated.guard
#print axioms PASoundness.PAtoCompactFirstAdditionOperandTransportAllocated.allocated_operand_transport
#print axioms PASoundness.PAtoCompactFirstAdditionOperandTransportAllocated.allocated_operand_transport_certificate
