import PASoundness.PAtoCompactMultiplicationReverseContextProjections
import PASoundness.PAtoCompactProductOldOutputWitnessClosed

/-! Old-output preimage for the exact shared successor context. The context
and membership are explicit object-level assumptions; neither the shared
graphs nor the suffix case or multiplication totality is established here. -/
namespace PASoundness.PAtoCompactMultiplicationOldReverseCommonContext
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactMultiplicationForwardSharedContext
open PASoundness.PAtoCompactMultiplicationReverseContextProjections
open PASoundness.PAtoCompactProductOldOutputPreimage
open PASoundness.PAtoCompactProductOldOutputWitnessFromReflection
open PASoundness.PAtoCompactProductOldOutputWitnessClosed
open PASoundness.PAtoCompactProductFullPrefixOldTripleReflection
open PASoundness.PAtoCompactProductOldSuffixExclusion
open PASoundness.PAtoCompactMultiplicationFullPrefixOldEdge
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- For an old-result output, the exact shared graph context yields its full
new-product preimage and uniqueness witness. -/
def old_reverse_case : KDerivation (imp context.encode
    (imp (member 32 5) targetWitness.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 32 5,context.encode]
  have hm : Context Γ (member 32 5) := .head _ _
  have hc : Context Γ context.encode := .hypothesis (by simp [Γ])
  have hn : Context Γ fullNoGarbage.encode := .mp hc (.closed project_noGarbage)
  have hs : Context Γ suffixClean.encode := .mp hc (.closed project_suffixClean)
  have hf : Context Γ (filterGraph 45 40 35 (neg (member 32 35))) := .mp hc (.closed project_filter)
  have hclean : Context Γ oldClean.encode := .mp hc (.closed project_oldClean)
  let inclusion : Formula := .all 9 (.imp (.member 10 9) (.member 64 9))
  have hi : Context Γ inclusion.encode := .mp hc (.closed project_inclusion)
  have hsucc : Context Γ (successorCode 30 38 39) := .mp hc (.closed project_successor)
  have hr : Context Γ oldReverse.encode := .mp hc (.closed project_oldReverse)
  have hh : Context Γ hypotheses.encode := by
    change Context Γ (both fullNoGarbage.encode (both suffixClean.encode
      (both (filterGraph 45 40 35 (neg (member 32 35))) (member 32 5))))
    exact Context.conjunctionIntro hn (Context.conjunctionIntro hs (Context.conjunctionIntro hf hm))
  exact .mp hr (.mp hsucc (.mp hi (.mp hclean (.mp hh (.closed old_output_unique)))))

theorem old_reverse_case_certificate : theoremCode (certificate old_reverse_case) =
    imp context.encode (imp (member 32 5) targetWitness.encode) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationOldReverseCommonContext
#print axioms PASoundness.PAtoCompactMultiplicationOldReverseCommonContext.old_reverse_case
#print axioms PASoundness.PAtoCompactMultiplicationOldReverseCommonContext.old_reverse_case_certificate
