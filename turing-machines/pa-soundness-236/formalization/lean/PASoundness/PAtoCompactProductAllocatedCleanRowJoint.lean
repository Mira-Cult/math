import PASoundness.PAtoCompactProductCleanRowJoint
import PASoundness.PAtoCompactProductAllocatedRaw303132

/-! The joint clean-old/suffix/row graph package with the actual allocated
multiplication relation as antecedent. It constructs no product successor. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductAllocatedCleanRowJoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactProductCleanRebased303132
open PASoundness.PAtoCompactProductAllocatedRaw303132
open PASoundness.PAtoCompactProductCleanRowJoint

/-- The allocated old product, source domain guard and suffix equivalence
construct one clean old graph and the same clean suffix map and row graph. -/
noncomputable def allocated_product_with_clean_suffix_and_row (base : Nat) : KDerivation
    (imp (mulAt 100 30 31 32).encode (imp (conditions base).encode jointResult.encode)) := by
  have hraw : KDerivation (imp (mulAt 100 30 31 32).encode oldProduct.encode) := by
    simpa [oldProduct,rawProduct] using allocated_to_raw
  exact compose hraw (product_with_clean_suffix_and_row base)

theorem allocated_product_with_clean_suffix_and_row_certificate (base : Nat) :
    theoremCode (certificate (allocated_product_with_clean_suffix_and_row base)) =
      imp (mulAt 100 30 31 32).encode (imp (conditions base).encode jointResult.encode) :=
  certificate_correct _
end PASoundness.PAtoCompactProductAllocatedCleanRowJoint
#print axioms PASoundness.PAtoCompactProductAllocatedCleanRowJoint.allocated_product_with_clean_suffix_and_row
#print axioms PASoundness.PAtoCompactProductAllocatedCleanRowJoint.allocated_product_with_clean_suffix_and_row_certificate
