import PASoundness.PAtoCompactMultiplicationForwardSharedContext
import PASoundness.PAtoCompactMultiplicationOldForwardJointShapes
import PASoundness.PAtoCompactMultiplicationOldForwardWitnessFullPrefix
import PASoundness.PAtoCompactMultiplicationForwardQuantGeneric

/-! The actual old-major point case for the common product-forward context.
All old/new graph witnesses and arithmetic hypotheses remain object-level
antecedents. This proves no product graph existence, multiplication totality,
or PA interpretation. -/
namespace PASoundness.PAtoCompactMultiplicationForwardOldShared
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactMultiplicationForwardSharedContext
open PASoundness.PAtoCompactMultiplicationLexSharedContext
open PASoundness.PAtoCompactMultiplicationNewRowSuffixOrder PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.PAtoCompactFixedFirstCoverageBase PASoundness.PAtoCompactFixedFirstPreservedBase
open PASoundness.PAtoCompactFixedFirstRowGraph64
open PASoundness.PAtoCompactMultiplicationOldForwardSpecialize
open PASoundness.PAtoCompactMultiplicationOldForwardWitnessClosed
open PASoundness.PAtoCompactMultiplicationOldForwardWitnessFullPrefix
open PASoundness.PAtoCompactMultiplicationOldForwardJointShapes
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def fullNoGarbage : Formula := replace 0 31 (noGarbage 64)
private def U : Formula := namedBoth (.member 30 3) (namedBoth fullNoGarbage
  PAtoCompactMultiplicationCleanOldMemberOutput.oldClean)
private def R : Formula := namedBoth oldPreserved64 (namedBoth (domainAt 100 45)
  (namedBoth PAtoCompactMultiplicationOldForwardWitnessClosed.cutAlternative U))

private theorem hypotheses_shape : replace 0 31 PAtoCompactMultiplicationOldForwardWitnessClosed.hypotheses = R := by decide
private theorem row_preserved_shape : oldPreserved 64 = oldPreserved64 := by decide
private theorem old_clean_shape : PAtoCompactMultiplicationCleanOldMemberOutput.oldClean =
    PAtoCompactMultiplicationLexSharedContext.oldCleanActual := by decide
private def oldTail : Formula :=
  replace 2 32 (replace 1 31 (replace 0 30 (replace 6 10 (namedBoth reverseFormula lexFormula))))
private theorem old_forward_shape : oldMatrixActual = namedBoth oldForward oldTail := by decide
private theorem witness_shape : Formula.ex 5 newOutput =
    PAtoCompactMultiplicationForwardQuantGeneric.witness := by decide

/-- From the common context and the two queried old-factor memberships, K
constructs the precise new-graph forward witness. The row, old product,
candidate-result and cut data are all retained in the context. -/
def old_point : KDerivation (imp context.encode
    (imp (member 30 3) (imp (member 31 4)
      PAtoCompactMultiplicationForwardQuantGeneric.witness.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 31 4,member 30 3,context.encode]
  have hb : Context Γ (member 31 4) := .head _ _
  have ha : Context Γ (member 30 3) := .hypothesis (by simp [Γ])
  have hc : Context Γ context.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ sharedPremise.encode := .mp hc (.closed project_shared)
  have hr : Context Γ rowBody64.encode := .mp hc (.closed project_row)
  have hs' : Context Γ (both oldMatrixActual.encode (both oldCleanActual.encode
      (both (domainAt 100 45).encode (both (domainAt 100 32).encode
        (both (domainAt 100 30).encode (both PAtoCompactMultiplicationLexSharedContext.cutAlternative.encode
          (both suffixFilter.encode (both suffixOrder.encode suffixClean.encode)))))))) := by
    simpa [sharedPremise,namedBoth,Formula.not,Formula.encode,both,neg] using hs
  have hm := Context.conjunctionLeft hs'
  have hclean := Context.conjunctionLeft (Context.conjunctionRight hs')
  have hremain := Context.conjunctionRight (Context.conjunctionRight hs')
  have hd := Context.conjunctionLeft hremain
  have hc' := Context.conjunctionLeft (Context.conjunctionRight
    (Context.conjunctionRight (Context.conjunctionRight hremain)))
  have hf : Context Γ oldForward.encode := by
    have ht : Context Γ (both oldForward.encode oldTail.encode) := by
      simpa [old_forward_shape,namedBoth,Formula.not,Formula.encode,both,neg] using hm
    exact Context.conjunctionLeft ht
  have hr' : Context Γ (replace 0 31 (rowInvariantPreserved 64)).encode := by
    simpa only [row_body64_shape] using hr
  have hp : Context Γ (both (oldPreserved 64).encode fullNoGarbage.encode) := by
    simpa [fullNoGarbage] using (Context.mp hr' (.closed row_projections))
  have hg : Context Γ oldPreserved64.encode := by
    simpa only [row_preserved_shape] using Context.conjunctionLeft hp
  have hn : Context Γ fullNoGarbage.encode := Context.conjunctionRight hp
  have hclean' : Context Γ PAtoCompactMultiplicationCleanOldMemberOutput.oldClean.encode := by
    simpa only [old_clean_shape] using hclean
  have hu : Context Γ U.encode := by
    have h := Context.conjunctionIntro ha (Context.conjunctionIntro hn hclean')
    simpa [U,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have halt : Context Γ PAtoCompactMultiplicationOldForwardWitnessClosed.cutAlternative.encode := by
    simpa [PAtoCompactMultiplicationLexSharedContext.cutAlternative,
      PAtoCompactMultiplicationOldForwardWitnessClosed.cutAlternative] using hc'
  have hR : Context Γ R.encode := by
    have h := Context.conjunctionIntro hg (Context.conjunctionIntro hd (Context.conjunctionIntro halt hu))
    simpa [R,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have hhex : Context Γ (replace 0 31 PAtoCompactMultiplicationOldForwardWitnessClosed.hypotheses).encode := by
    simpa only [hypotheses_shape] using hR
  have hw := Context.mp hb (Context.mp hf (Context.mp hhex (.closed old_forward_full_prefix)))
  change Context Γ (Formula.ex 5 newOutput).encode at hw
  rw [witness_shape] at hw
  exact hw

theorem old_point_certificate : theoremCode (certificate old_point) =
    imp context.encode (imp (member 30 3) (imp (member 31 4)
      PAtoCompactMultiplicationForwardQuantGeneric.witness.encode)) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationForwardOldShared
#print axioms PASoundness.PAtoCompactMultiplicationForwardOldShared.old_point
#print axioms PASoundness.PAtoCompactMultiplicationForwardOldShared.old_point_certificate
