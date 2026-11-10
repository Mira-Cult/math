import PASoundness.PAtoCompactAdditionZeroAllocated
import PASoundness.PAtoCompactFirstAdditionCutAllocation
import PASoundness.PAtoCompactSecondAdditionCutAllocation
import PASoundness.PAtoCompactScopedActiveReplace

/-! Capture-safe finite K transport from the base-100 allocated addition
relation to the two raw instances used in the output-functionality proof. -/
namespace PASoundness.PAtoCompactAllocatedAdditionToRaw

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAdditionZeroAllocated PASoundness.PAtoCompactAddBaseInventory
open PASoundness.PAtoCompactScopedActiveReplace

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def frame : Formula := .imp (addAt 100 30 31 32) additionFormula
private def moved28 : Formula := replace 30 28 frame
private def moved1 : Formula := replace 31 1 moved28
private theorem template_eq : addTemplate = additionFormula := by decide

private def base : KDerivation frame.encode := by
  have h := original_allocated_alpha 100 (by decide)
  rw [template_eq] at h
  exact h.backward

def firstFrame : Formula := .imp (addAt 100 28 1 0)
  PASoundness.PAtoCompactFirstAdditionCutAllocation.addition
def secondFrame : Formula := .imp (addAt 100 28 1 8)
  PASoundness.PAtoCompactSecondAdditionCutAllocation.addition

/-- The first base-100 allocated relation supplies its literal raw instance. -/
def first_allocated_to_raw : KDerivation firstFrame.encode := by
  have h28 := replace_derivation 30 28 frame (by decide) (by decide) base
  have h1 := replace_derivation 31 1 moved28 (by decide) (by decide) (by simpa only [moved28] using h28)
  have h0 := replace_derivation 32 0 moved1 (by decide) (by decide) (by simpa only [moved1] using h1)
  have halign : replace 32 0 moved1 = firstFrame := by decide
  rw [halign] at h0
  exact h0

/-- The second base-100 allocated relation supplies its literal raw instance. -/
def second_allocated_to_raw : KDerivation secondFrame.encode := by
  have h28 := replace_derivation 30 28 frame (by decide) (by decide) base
  have h1 := replace_derivation 31 1 moved28 (by decide) (by decide) (by simpa only [moved28] using h28)
  have h8 := replace_derivation 32 8 moved1 (by decide) (by decide) (by simpa only [moved1] using h1)
  have halign : replace 32 8 moved1 = secondFrame := by decide
  rw [halign] at h8
  exact h8

theorem first_allocated_to_raw_certificate : theoremCode (certificate first_allocated_to_raw) = firstFrame.encode :=
  certificate_correct first_allocated_to_raw
theorem second_allocated_to_raw_certificate : theoremCode (certificate second_allocated_to_raw) = secondFrame.encode :=
  certificate_correct second_allocated_to_raw

end PASoundness.PAtoCompactAllocatedAdditionToRaw

#print axioms PASoundness.PAtoCompactAllocatedAdditionToRaw.first_allocated_to_raw
#print axioms PASoundness.PAtoCompactAllocatedAdditionToRaw.second_allocated_to_raw
#print axioms PASoundness.PAtoCompactAllocatedAdditionToRaw.firstFrame
#print axioms PASoundness.PAtoCompactAllocatedAdditionToRaw.secondFrame
#print axioms PASoundness.PAtoCompactAllocatedAdditionToRaw.first_allocated_to_raw_certificate
#print axioms PASoundness.PAtoCompactAllocatedAdditionToRaw.second_allocated_to_raw_certificate
