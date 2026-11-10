import PASoundness.PAtoCompactProductOriginalAllocatedAlpha

/-! Capture-safe K transport between the raw multiplication formulas used in
successor construction and the allocated formulas at base 300. This supplies
both directions at each of the two displayed triples of labels; it does not
assert multiplication totality or construct a product graph. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationAllocatedStepTransport
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactProductOriginalAllocatedAlpha
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Raw old product, with first/second/result names 204,30,32. -/
def oldRaw : Formula := replace 2 32 (replace 1 30 (replace 0 204 productFormula))
/-- Raw new product, with first/second/result names 205,30,45. -/
def newRaw : Formula := replace 2 45 (replace 1 30 (replace 0 205 productFormula))
private def originalForward : Formula := .imp productFormula (mulAt 300 0 1 2)
private def originalBackward : Formula := .imp (mulAt 300 0 1 2) productFormula

private noncomputable def old_specialize (f : Formula) (d : KDerivation f.encode)
    (h0 : 0 ∉ f.binders) (h204 : 204 ∉ f.binders)
    (h1 : 1 ∉ f.binders) (h30 : 30 ∉ f.binders)
    (h2 : 2 ∉ f.binders) (h32 : 32 ∉ f.binders) :
    KDerivation (replace 2 32 (replace 1 30 (replace 0 204 f))).encode := by
  have h0' := universalInstance 0 204 f (by decide) h0 h204
  have d0 : KDerivation (replace 0 204 f).encode := .mp (.generalize 0 d) h0'
  have h1' := universalInstance 1 30 (replace 0 204 f) (by decide)
    (by simpa only [replace_binders] using h1) (by simpa only [replace_binders] using h30)
  have d1 : KDerivation (replace 1 30 (replace 0 204 f)).encode := .mp (.generalize 1 d0) h1'
  have h2' := universalInstance 2 32 (replace 1 30 (replace 0 204 f)) (by decide)
    (by simpa only [replace_binders] using h2) (by simpa only [replace_binders] using h32)
  exact .mp (.generalize 2 d1) h2'

private noncomputable def new_specialize (f : Formula) (d : KDerivation f.encode)
    (h0 : 0 ∉ f.binders) (h205 : 205 ∉ f.binders)
    (h1 : 1 ∉ f.binders) (h30 : 30 ∉ f.binders)
    (h2 : 2 ∉ f.binders) (h45 : 45 ∉ f.binders) :
    KDerivation (replace 2 45 (replace 1 30 (replace 0 205 f))).encode := by
  have h0' := universalInstance 0 205 f (by decide) h0 h205
  have d0 : KDerivation (replace 0 205 f).encode := .mp (.generalize 0 d) h0'
  have h1' := universalInstance 1 30 (replace 0 205 f) (by decide)
    (by simpa only [replace_binders] using h1) (by simpa only [replace_binders] using h30)
  have d1 : KDerivation (replace 1 30 (replace 0 205 f)).encode := .mp (.generalize 1 d0) h1'
  have h2' := universalInstance 2 45 (replace 1 30 (replace 0 205 f)) (by decide)
    (by simpa only [replace_binders] using h2) (by simpa only [replace_binders] using h45)
  exact .mp (.generalize 2 d1) h2'

private theorem old_forward_shape : replace 2 32 (replace 1 30 (replace 0 204 originalForward)) =
    .imp oldRaw (mulAt 300 204 30 32) := by decide
private theorem old_backward_shape : replace 2 32 (replace 1 30 (replace 0 204 originalBackward)) =
    .imp (mulAt 300 204 30 32) oldRaw := by decide
private theorem new_forward_shape : replace 2 45 (replace 1 30 (replace 0 205 originalForward)) =
    .imp newRaw (mulAt 300 205 30 45) := by decide
private theorem new_backward_shape : replace 2 45 (replace 1 30 (replace 0 205 originalBackward)) =
    .imp (mulAt 300 205 30 45) newRaw := by decide

/-- Old raw multiplication implies the allocated formula. -/
noncomputable def old_raw_to_allocated : KDerivation (imp oldRaw.encode (mulAt 300 204 30 32).encode) := by
  have h := old_specialize originalForward (original_allocated_alpha 300 (by decide)).forward
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [old_forward_shape] at h
  exact h
/-- Old allocated multiplication implies the raw formula. -/
noncomputable def old_allocated_to_raw : KDerivation (imp (mulAt 300 204 30 32).encode oldRaw.encode) := by
  have h := old_specialize originalBackward (original_allocated_alpha 300 (by decide)).backward
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [old_backward_shape] at h
  exact h
/-- New raw multiplication implies the allocated formula. -/
noncomputable def new_raw_to_allocated : KDerivation (imp newRaw.encode (mulAt 300 205 30 45).encode) := by
  have h := new_specialize originalForward (original_allocated_alpha 300 (by decide)).forward
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [new_forward_shape] at h
  exact h
/-- New allocated multiplication implies the raw formula. -/
noncomputable def new_allocated_to_raw : KDerivation (imp (mulAt 300 205 30 45).encode newRaw.encode) := by
  have h := new_specialize originalBackward (original_allocated_alpha 300 (by decide)).backward
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [new_backward_shape] at h
  exact h

theorem old_raw_to_allocated_certificate : theoremCode (certificate old_raw_to_allocated) =
    imp oldRaw.encode (mulAt 300 204 30 32).encode := certificate_correct _
theorem old_allocated_to_raw_certificate : theoremCode (certificate old_allocated_to_raw) =
    imp (mulAt 300 204 30 32).encode oldRaw.encode := certificate_correct _
theorem new_raw_to_allocated_certificate : theoremCode (certificate new_raw_to_allocated) =
    imp newRaw.encode (mulAt 300 205 30 45).encode := certificate_correct _
theorem new_allocated_to_raw_certificate : theoremCode (certificate new_allocated_to_raw) =
    imp (mulAt 300 205 30 45).encode newRaw.encode := certificate_correct _
end PASoundness.PAtoCompactMultiplicationAllocatedStepTransport
#print axioms PASoundness.PAtoCompactMultiplicationAllocatedStepTransport.old_raw_to_allocated
#print axioms PASoundness.PAtoCompactMultiplicationAllocatedStepTransport.old_allocated_to_raw
#print axioms PASoundness.PAtoCompactMultiplicationAllocatedStepTransport.new_raw_to_allocated
#print axioms PASoundness.PAtoCompactMultiplicationAllocatedStepTransport.new_allocated_to_raw
