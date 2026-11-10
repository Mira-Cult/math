import PASoundness.PAtoCompactMemberCutQuotientChains

/-! Align the quotient-chain conclusions with the exact target-witness syntax
obtained by capture-safe replacement of the original cut/suffix names. -/
namespace PASoundness.PAtoCompactMemberCutQuotientTargetShape
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactMemberCutQuotientChains

set_option maxRecDepth 262144
set_option maxHeartbeats 0

def targetCut : Formula := replace 33 41 (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33)
def targetSuffix : Formula := replace 34 38 (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34)
def targetConclusion : Formula := namedBoth targetCut targetSuffix

/-- The target labels are syntactically fresh for the raw quotient binders;
this identifies the replacement result, without requiring distinct objects. -/
theorem target_cut_shape : targetCut = PASoundness.PAtoCompactOrdinalAddition.equivAt 30 41 := by decide

theorem target_suffix_shape : targetSuffix = PASoundness.PAtoCompactOrdinalAddition.equivAt 31 38 := by decide

/-- Both component-equivalence fields in the exact target-introduction form. -/
def target_chains : KDerivation (imp guard.encode targetConclusion.encode) := by
  simpa only [targetConclusion, rawConclusion, target_cut_shape, target_suffix_shape] using raw_chains

theorem target_chains_certificate : theoremCode (certificate target_chains) =
    imp guard.encode targetConclusion.encode := certificate_correct target_chains

end PASoundness.PAtoCompactMemberCutQuotientTargetShape

#print axioms PASoundness.PAtoCompactMemberCutQuotientTargetShape.target_chains
#print axioms PASoundness.PAtoCompactMemberCutQuotientTargetShape.target_chains_certificate
