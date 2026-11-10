import PASoundness.PAtoCompactSeededSpanAdditionCutAlignment
import PASoundness.PAtoCompactFirstSpanPathOutside
import PASoundness.PAtoCompactSuffixCleanWitness
import PASoundness.PAtoCompactSeededSpanCutCandidate

/-! Allocate the cut and suffix witnesses of one literal addition formula at
40 and 31. Both existential renamings are capture-checked K proof data. -/
namespace PASoundness.PAtoCompactFirstAdditionCutAllocation

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactSeededSpanCutCandidate PASoundness.PAtoCompactFirstSpanPathOutside
open PASoundness.PAtoCompactSuffixCleanWitness PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def addition : Formula := replace 32 0 (replace 31 1 (replace 30 28 additionFormula))
def allocatedBody : Formula := namedBoth sourceRelation (namedBoth firstEquivalence
  (namedBoth PASoundness.PAtoCompactFirstSpanPathOutside.suffixFilter suffixEquivalence))
def allocated : Formula := .ex 40 (.ex 31 allocatedBody)

private def rawBody : Formula := namedBoth (namedEither (.equal 33 32) (.member 32 33))
  (namedBoth (equivAt 30 33) (namedBoth suffixFormula (equivAt 31 34)))
private def instantiatedBody : Formula := replace 32 0 (replace 31 1 (replace 30 28 rawBody))
private def cutBody : Formula := replace 33 40 instantiatedBody

private theorem addition_shape : addition = .ex 33 (.ex 34 instantiatedBody) := by decide
private theorem cut_shape : replace 33 40 (.ex 34 instantiatedBody) = .ex 34 cutBody := by decide
private theorem body_shape : replace 34 31 cutBody = allocatedBody := by decide

/-- The actual addition cut and suffix are retained in that order; no
candidate, graph existence or extra semantic principle is used. -/
def allocate_first_addition : KDerivation (imp addition.encode allocated.encode) := by
  have hcut := (existentialAlpha 33 40 (.ex 34 instantiatedBody) (by decide) (by decide) (by decide)).1
  rw [cut_shape] at hcut
  have hsuffix := (existentialAlpha 34 31 cutBody (by decide) (by decide) (by decide)).1
  have h := compose hcut (existsCongr 40 hsuffix)
  rw [body_shape] at h
  rw [addition_shape]
  simpa only [allocated, Formula.encode] using h

theorem allocate_first_addition_certificate : theoremCode (certificate allocate_first_addition) =
    imp addition.encode allocated.encode := certificate_correct allocate_first_addition

end PASoundness.PAtoCompactFirstAdditionCutAllocation

#print axioms PASoundness.PAtoCompactFirstAdditionCutAllocation.addition
#print axioms PASoundness.PAtoCompactFirstAdditionCutAllocation.allocatedBody
#print axioms PASoundness.PAtoCompactFirstAdditionCutAllocation.allocated
#print axioms PASoundness.PAtoCompactFirstAdditionCutAllocation.allocate_first_addition
#print axioms PASoundness.PAtoCompactFirstAdditionCutAllocation.allocate_first_addition_certificate
