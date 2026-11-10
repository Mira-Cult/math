import PASoundness.PAtoCompactSecondAdditionCutAllocation
import PASoundness.PAtoCompactAdditionZeroAllocated
import PASoundness.PAtoCompactScopedActiveReplace

/-! Capture-safe K conversion from the second literal addition instance to
its base-100 allocated presentation. No existence, uniqueness or output
transport theorem is claimed. -/
namespace PASoundness.PAtoCompactSecondAdditionRawAllocatedIntro

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAdditionZeroAllocated PASoundness.PAtoCompactAddBaseInventory
open PASoundness.PAtoCompactScopedActiveReplace

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def frame : Formula := .imp additionFormula (addAt 100 30 31 32)
private def moved28 : Formula := replace 30 28 frame
private def moved1 : Formula := replace 31 1 moved28
private theorem template_eq : addTemplate = additionFormula := by decide

/-- A literal addition with inputs 28,1 and output 8 gives its actual
base-100 allocated relation by explicit capture-safe finite K replacement.
The labels are syntactic; their assigned objects may coincide. -/
def second_raw_to_allocated : KDerivation
    (imp PASoundness.PAtoCompactSecondAdditionCutAllocation.addition.encode
      (addAt 100 28 1 8).encode) := by
  have hbase : KDerivation frame.encode := by
    have h := original_allocated_alpha 100 (by decide)
    rw [template_eq] at h
    exact h.forward
  have h28 := replace_derivation 30 28 frame (by decide) (by decide) hbase
  have h1 := replace_derivation 31 1 moved28 (by decide) (by decide)
    (by simpa only [moved28] using h28)
  have h8 := replace_derivation 32 8 moved1 (by decide) (by decide)
    (by simpa only [moved1] using h1)
  have halign : replace 32 8 moved1 =
      .imp PASoundness.PAtoCompactSecondAdditionCutAllocation.addition (addAt 100 28 1 8) := by decide
  rw [halign] at h8
  simpa only [Formula.encode] using h8


/-- The literal addition at source inputs 30,31 and target output 8. -/
def outputOnly : Formula := replace 32 8 additionFormula

/-- Replacing only the result name in the same finite K alpha proof yields
allocated addition for unchanged inputs 30,31 and output 8. -/
def raw_output_to_allocated : KDerivation
    (imp outputOnly.encode (addAt 100 30 31 8).encode) := by
  have hbase : KDerivation frame.encode := by
    have h := original_allocated_alpha 100 (by decide)
    rw [template_eq] at h
    exact h.forward
  have h8 := replace_derivation 32 8 frame (by decide) (by decide) hbase
  have halign : replace 32 8 frame = .imp outputOnly (addAt 100 30 31 8) := by decide
  rw [halign] at h8
  simpa only [Formula.encode] using h8

theorem raw_output_to_allocated_certificate :
    theoremCode (certificate raw_output_to_allocated) =
      imp outputOnly.encode (addAt 100 30 31 8).encode := certificate_correct raw_output_to_allocated

theorem second_raw_to_allocated_certificate :
    theoremCode (certificate second_raw_to_allocated) =
      imp PASoundness.PAtoCompactSecondAdditionCutAllocation.addition.encode
        (addAt 100 28 1 8).encode := certificate_correct second_raw_to_allocated

end PASoundness.PAtoCompactSecondAdditionRawAllocatedIntro

#print axioms PASoundness.PAtoCompactSecondAdditionRawAllocatedIntro.second_raw_to_allocated
#print axioms PASoundness.PAtoCompactSecondAdditionRawAllocatedIntro.second_raw_to_allocated_certificate

#print axioms PASoundness.PAtoCompactSecondAdditionRawAllocatedIntro.outputOnly
#print axioms PASoundness.PAtoCompactSecondAdditionRawAllocatedIntro.raw_output_to_allocated
#print axioms PASoundness.PAtoCompactSecondAdditionRawAllocatedIntro.raw_output_to_allocated_certificate
