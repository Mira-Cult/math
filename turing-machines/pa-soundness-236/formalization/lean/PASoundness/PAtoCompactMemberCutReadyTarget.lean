import PASoundness.PAtoCompactMemberCutQuotientTargetShape
import PASoundness.PAtoCompactMemberCutAllocatedTargetIntro

/-! Combine explicitly supplied quotient chains and a selected target cut and
suffix into target addition. This does not construct those supplied facts or
eliminate the old/new cut and suffix witnesses. -/
namespace PASoundness.PAtoCompactMemberCutReadyTarget
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMemberCutQuotientChains PASoundness.PAtoCompactMemberCutQuotientTargetShape
open PASoundness.PAtoCompactMemberCutRawTargetIntro PASoundness.PAtoCompactMemberCutAllocatedTargetIntro
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The quotient-chain guard retains both operand domains, original witness
isomorphisms and supplied old-to-new cut/suffix isomorphisms. -/
def ready : Formula := namedBoth guard (namedBoth (.member 8 41) PAtoCompactMemberCutRawTargetIntro.targetSuffix)

/-- Once the displayed actual target cut/suffix and quotient relations are
supplied, K constructs target addition at the original operands. The names
33,34,41,38 remain free here; no existential choice is asserted. -/
def addition_of_ready : KDerivation (imp ready.encode (addAt 100 30 31 8).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [ready.encode]
  have hr : Context Γ ready.encode := .head _ _
  have hg : Context Γ guard.encode := Context.conjunctionLeft hr
  have htail := Context.conjunctionRight hr
  have hm : Context Γ (member 8 41) := Context.conjunctionLeft htail
  have hs : Context Γ PAtoCompactMemberCutRawTargetIntro.targetSuffix.encode := Context.conjunctionRight htail
  have hc : Context Γ targetConclusion.encode := .mp hg (.closed target_chains)
  have hcut : Context Γ targetCutEquivalence.encode := by
    have h := Context.conjunctionLeft hc
    simpa only [targetConclusion, PAtoCompactMemberCutQuotientTargetShape.targetCut,
      targetCutEquivalence] using h
  have he : Context Γ targetSuffixEquivalence.encode := by
    have h := Context.conjunctionRight hc
    simpa only [targetConclusion, PAtoCompactMemberCutQuotientTargetShape.targetSuffix,
      targetSuffixEquivalence] using h
  exact .mp he (.mp hs (.mp hcut (.mp hm (.closed allocated_target_from_member_cut))))

theorem addition_of_ready_certificate : theoremCode (certificate addition_of_ready) =
    imp ready.encode (addAt 100 30 31 8).encode := certificate_correct addition_of_ready
end PASoundness.PAtoCompactMemberCutReadyTarget

#print axioms PASoundness.PAtoCompactMemberCutReadyTarget.addition_of_ready
#print axioms PASoundness.PAtoCompactMemberCutReadyTarget.addition_of_ready_certificate
