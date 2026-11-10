import PASoundness.PAtoCompactMemberCutRawTargetIntro
import PASoundness.PAtoCompactSecondAdditionRawAllocatedIntro

/-! The literal target introduced from supplied cut/suffix facts transports
to the allocated target addition. No input fact or graph is constructed. -/
namespace PASoundness.PAtoCompactMemberCutAllocatedTargetIntro
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMemberCutRawTargetIntro PASoundness.PAtoCompactSecondAdditionRawAllocatedIntro
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Supplied target-cut membership, its left-operand isomorphism, the target
suffix and its right-operand isomorphism imply the allocated addition. The
same 41/38 witnesses are retained; object values may coincide. -/
def allocated_target_from_member_cut : KDerivation
    (imp (member 8 41) (imp targetCutEquivalence.encode
      (imp targetSuffix.encode (imp targetSuffixEquivalence.encode
        (addAt 100 30 31 8).encode)))) := by
  have hc : KDerivation (imp targetAddition.encode (addAt 100 30 31 8).encode) := by
    simpa only [targetAddition,outputOnly] using raw_output_to_allocated
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [targetSuffixEquivalence.encode,targetSuffix.encode,targetCutEquivalence.encode,member 8 41]
  have he : Context Γ targetSuffixEquivalence.encode := .head _ _
  have hf : Context Γ targetSuffix.encode := .hypothesis (by simp [Γ])
  have hc' : Context Γ targetCutEquivalence.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 8 41) := .hypothesis (by simp [Γ])
  have hr : Context Γ targetAddition.encode :=
    .mp he (.mp hf (.mp hc' (.mp hm (.closed target_from_member_cut))))
  exact .mp hr (.closed hc)

theorem allocated_target_from_member_cut_certificate :
    theoremCode (certificate allocated_target_from_member_cut) =
      imp (member 8 41) (imp targetCutEquivalence.encode
        (imp targetSuffix.encode (imp targetSuffixEquivalence.encode
          (addAt 100 30 31 8).encode))) := certificate_correct _
end PASoundness.PAtoCompactMemberCutAllocatedTargetIntro

#print axioms PASoundness.PAtoCompactMemberCutAllocatedTargetIntro.allocated_target_from_member_cut
#print axioms PASoundness.PAtoCompactMemberCutAllocatedTargetIntro.allocated_target_from_member_cut_certificate
