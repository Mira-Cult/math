import PASoundness.PAtoCompactProductOriginalAllocatedAlpha

/-! Capture-safe K alpha transport between the allocated multiplication graph
at base 100 and the raw product formula on input labels 30, 31 and 32.  This
is only formula transport: it does not construct a product, prove a product
successor law, or establish PA soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductAllocatedRaw303132
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactProductOriginalAllocatedAlpha
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The raw multiplication formula at the old-product input names. -/
def rawProduct : Formula := replace 2 32 (replace 1 31 (replace 0 30 productFormula))
private def forwardStatement : Formula := .imp productFormula (mulAt 100 0 1 2)
private def backwardStatement : Formula := .imp (mulAt 100 0 1 2) productFormula
private def specialize (f : Formula) : Formula := replace 2 32 (replace 1 31 (replace 0 30 f))

private noncomputable def specialize_proof (f : Formula) (h : KDerivation f.encode)
    (h0 : 0 ∉ f.binders) (h30 : 30 ∉ f.binders)
    (h1 : 1 ∉ f.binders) (h31 : 31 ∉ f.binders)
    (h2 : 2 ∉ f.binders) (h32 : 32 ∉ f.binders) :
    KDerivation (specialize f).encode := by
  let f0 := replace 0 30 f
  let f1 := replace 1 31 f0
  have hfirst : KDerivation f0.encode := .mp (.generalize 0 h)
    (universalInstance 0 30 f (by decide) h0 h30)
  have hsecond : KDerivation f1.encode := .mp (.generalize 1 hfirst)
    (universalInstance 1 31 f0 (by decide)
      (by simpa [f0,replace_binders] using h1)
      (by simpa [f0,replace_binders] using h31))
  have hthird : KDerivation (replace 2 32 f1).encode := .mp (.generalize 2 hsecond)
    (universalInstance 2 32 f1 (by decide)
      (by simpa [f1,f0,replace_binders] using h2)
      (by simpa [f1,f0,replace_binders] using h32))
  exact hthird

private theorem forward_shape : specialize forwardStatement =
    .imp rawProduct (mulAt 100 30 31 32) := by decide
private theorem backward_shape : specialize backwardStatement =
    .imp (mulAt 100 30 31 32) rawProduct := by decide

/-- Capture-safe K transport from the raw product relation. -/
noncomputable def raw_to_allocated : KDerivation
    (imp rawProduct.encode (mulAt 100 30 31 32).encode) := by
  have h := (original_allocated_alpha 100 (by decide)).forward
  have hh := specialize_proof forwardStatement h (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [forward_shape] at hh
  exact hh

/-- Reverse K transport preserves the same three input labels. -/
noncomputable def allocated_to_raw : KDerivation
    (imp (mulAt 100 30 31 32).encode rawProduct.encode) := by
  have h := (original_allocated_alpha 100 (by decide)).backward
  have hh := specialize_proof backwardStatement h (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  rw [backward_shape] at hh
  exact hh

theorem raw_allocated_forward_certificate :
    theoremCode (certificate raw_to_allocated) =
      imp rawProduct.encode (mulAt 100 30 31 32).encode := certificate_correct _
theorem raw_allocated_backward_certificate :
    theoremCode (certificate allocated_to_raw) =
      imp (mulAt 100 30 31 32).encode rawProduct.encode := certificate_correct _
end PASoundness.PAtoCompactProductAllocatedRaw303132
#print axioms PASoundness.PAtoCompactProductAllocatedRaw303132.raw_to_allocated
#print axioms PASoundness.PAtoCompactProductAllocatedRaw303132.allocated_to_raw
#print axioms PASoundness.PAtoCompactProductAllocatedRaw303132.raw_allocated_forward_certificate
#print axioms PASoundness.PAtoCompactProductAllocatedRaw303132.raw_allocated_backward_certificate
