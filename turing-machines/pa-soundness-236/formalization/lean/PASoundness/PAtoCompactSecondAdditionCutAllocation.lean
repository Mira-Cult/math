import PASoundness.PAtoCompactSeededSpanAdditionCutAlignment
import PASoundness.PAtoCompactFirstSpanTargetOutside
import PASoundness.PAtoCompactSuffixCleanWitness
import PASoundness.PAtoCompactSeededSpanCutCandidate

/-! Allocate the cut and suffix witnesses of a second literal addition
formula at 41 and 38, using capture-checked K existential alpha conversion. -/
namespace PASoundness.PAtoCompactSecondAdditionCutAllocation

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactSeededSpanCutCandidate PASoundness.PAtoCompactFirstSpanTargetOutside
open PASoundness.PAtoCompactSuffixCleanWitness PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def addition : Formula := replace 32 8 (replace 31 1 (replace 30 28 additionFormula))
def suffixEquivalence38 : Formula := replace 31 38 suffixEquivalence
def allocatedBody : Formula := namedBoth targetRelation (namedBoth secondEquivalence
  (namedBoth targetFilter suffixEquivalence38))
def allocated : Formula := .ex 41 (.ex 38 allocatedBody)

private def rawBody : Formula := namedBoth (namedEither (.equal 33 32) (.member 32 33))
  (namedBoth (equivAt 30 33) (namedBoth suffixFormula (equivAt 31 34)))
private def instantiatedBody : Formula := replace 32 8 (replace 31 1 (replace 30 28 rawBody))
private def cutBody : Formula := replace 33 41 instantiatedBody

private theorem addition_shape : addition = .ex 33 (.ex 34 instantiatedBody) := by decide
private theorem cut_shape : replace 33 41 (.ex 34 instantiatedBody) = .ex 34 cutBody := by decide
private theorem body_shape : replace 34 38 cutBody = allocatedBody := by decide

/-- The actual second cut and suffix witnesses are preserved. -/
def allocate_second_addition : KDerivation (imp addition.encode allocated.encode) := by
  have hcut := (existentialAlpha 33 41 (.ex 34 instantiatedBody) (by decide) (by decide) (by decide)).1
  rw [cut_shape] at hcut
  have hsuffix := (existentialAlpha 34 38 cutBody (by decide) (by decide) (by decide)).1
  have h := compose hcut (existsCongr 41 hsuffix)
  rw [body_shape] at h
  rw [addition_shape]
  simpa only [allocated, Formula.encode] using h

theorem allocate_second_addition_certificate : theoremCode (certificate allocate_second_addition) =
    imp addition.encode allocated.encode := certificate_correct allocate_second_addition

end PASoundness.PAtoCompactSecondAdditionCutAllocation

#print axioms PASoundness.PAtoCompactSecondAdditionCutAllocation.addition
#print axioms PASoundness.PAtoCompactSecondAdditionCutAllocation.suffixEquivalence38
#print axioms PASoundness.PAtoCompactSecondAdditionCutAllocation.allocatedBody
#print axioms PASoundness.PAtoCompactSecondAdditionCutAllocation.allocated
#print axioms PASoundness.PAtoCompactSecondAdditionCutAllocation.allocate_second_addition
#print axioms PASoundness.PAtoCompactSecondAdditionCutAllocation.allocate_second_addition_certificate
