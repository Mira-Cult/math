import PASoundness.PAtoCompactAdditionEquivZeroRight
import PASoundness.PAtoCompactUnaryGraphFunctional

/-! Output transport for the zero graph. -/
namespace PASoundness.PAtoCompactZeroGraphOutput

open FirstOrder
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactUnaryGraphFunctional
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactTemplateBlockShift PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactZeroBaseTransport PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactAdditionEquivZeroRight PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactEquivNoShadow

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

private def source : Formula :=
  .imp (.all 36 (Formula.member 31 36).not)
    (.imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34)
      (.all 37 (Formula.member 34 37).not))

def canonicalZeroOutput : Formula :=
  .imp (.all 36 (Formula.member 0 36).not)
    (.imp equivalentFormula (.all 37 (Formula.member 1 37).not))

private def source_proof : KDerivation source.encode := by
  change KDerivation (imp (zeroCode 31 36)
    (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode (zeroCode 34 37)))
  exact addition_equiv_zero_right

def canonical_zero_output : KDerivation canonicalZeroOutput.encode := by
  have h0 := replace_derivation 31 0 source (by decide) (by decide) source_proof
  have h1 := replace_derivation 34 1 (replace 31 0 source) (by decide) (by decide) h0
  have he : replace 34 1 (replace 31 0 source) = canonicalZeroOutput := by decide
  simpa only [he] using h1

/-- Certificate for the fixed 0/1 output-transport derivation. -/
theorem canonical_zero_output_certificate :
    theoremCode (certificate canonical_zero_output) = canonicalZeroOutput.encode :=
  certificate_correct _

end PASoundness.PAtoCompactZeroGraphOutput

#print axioms PASoundness.PAtoCompactZeroGraphOutput.canonical_zero_output
#print axioms PASoundness.PAtoCompactZeroGraphOutput.canonical_zero_output_certificate
