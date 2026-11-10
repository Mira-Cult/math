import PASoundness.PAtoCompactMemberChosenConditional
import PASoundness.PAtoCompactSelectedCutRenamedAllocated
import PASoundness.PAtoCompactSuffixRebaseAllocatedBridge

/-! The fixed original-graph guard supplies the two proof-data inputs of the
conditional target cut/suffix collector. This module does not construct the
guard or eliminate the original graph witness. -/
namespace PASoundness.PAtoCompactMemberChosenGuardInputs
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactLessRightSegmentAliases
open PASoundness.PAtoCompactSelectedCutRenamedGuard PASoundness.PAtoCompactSelectedCutRenamedAllocated
open PASoundness.PAtoCompactMemberChosenConditional
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The same original graph60 supplies both order and bijection; the source
proper cut, source suffix and both outer transitivity premises are retained. -/
def guard : Formula := namedBoth (namedTrans 32 11 12) (namedBoth (namedTrans 8 16 18)
  (namedBoth (.member 32 33) (namedBoth suffixFormula (namedBoth targetOrder targetBijection))))

/-- The original graph supplies a single selected cut with the required
membership, original edge, and allocated cut equivalence. -/
def guard_cut : KDerivation (imp guard.encode (existsCode 41 cutBody.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hs : Context Γ (namedTrans 32 11 12).encode := Context.conjunctionLeft hg
  have h := Context.conjunctionRight hg
  have ht : Context Γ (namedTrans 8 16 18).encode := Context.conjunctionLeft h
  have h := Context.conjunctionRight h
  have hm : Context Γ (member 32 33) := Context.conjunctionLeft h
  have h := Context.conjunctionRight h
  have h := Context.conjunctionRight h
  have ho : Context Γ targetOrder.encode := Context.conjunctionLeft h
  have hb : Context Γ targetBijection.encode := Context.conjunctionRight h
  have hc : Context Γ allocatedSelected.encode :=
    .mp hb (.mp ho (.mp hm (.mp ht (.mp hs (.closed selected_cut_renamed_allocated)))))
  simpa only [allocatedSelected,allocatedBody,cutBody,Formula.encode] using hc

/-- Under the same guard and selected cut body, the supplied actual target
suffix is allocated-equivalent to the old suffix. The original graph edge
is projected from that same cut body rather than chosen again. -/
noncomputable def guard_suffix : KDerivation
    (imp guard.encode (imp cutBody.encode
      (imp PAtoCompactMemberCutRawTargetIntro.targetSuffix.encode (PASoundness.PAtoCompactTermTranslation.equivAt 100 34 38).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let T := PAtoCompactMemberCutRawTargetIntro.targetSuffix.encode
  let Γ := [T,cutBody.encode,guard.encode]
  have hsuf : Context Γ T := .head _ _
  have hcut : Context Γ cutBody.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ guard.encode := .hypothesis (by simp [Γ])
  have h := Context.conjunctionRight hg
  have h := Context.conjunctionRight h
  have hm : Context Γ (member 32 33) := Context.conjunctionLeft h
  have h := Context.conjunctionRight h
  have hold : Context Γ suffixFormula.encode := Context.conjunctionLeft h
  have h := Context.conjunctionRight h
  have ho : Context Γ targetOrder.encode := Context.conjunctionLeft h
  have hb : Context Γ targetBijection.encode := Context.conjunctionRight h
  have hp := Context.conjunctionLeft hcut
  have hn : Context Γ (member 8 41) := Context.conjunctionLeft hp
  have he : Context Γ (graphFormula 60 33 41).encode := Context.conjunctionRight hp
  have ho' : Context Γ (PAtoCompactSuffixRebaseMatrixAlpha.relabel orderFormula).encode := by
    simpa only [targetOrder,PAtoCompactSuffixRebaseMatrixAlpha.relabel] using ho
  have hb' : Context Γ (PAtoCompactSuffixRebaseMatrixAlpha.relabel bijectionFormula).encode := by
    simpa only [targetBijection,PAtoCompactSuffixRebaseMatrixAlpha.relabel] using hb
  have hsuf' : Context Γ PAtoCompactSuffixRebaseFilterAlpha.targetSuffix.encode := by
    simpa only [T,PAtoCompactMemberCutRawTargetIntro.targetSuffix,PAtoCompactSuffixRebaseFilterAlpha.targetSuffix] using hsuf
  exact .mp hb' (.mp he (.mp hn (.mp hm (.mp hsuf' (.mp hold (.mp ho'
    (.closed PAtoCompactSuffixRebaseAllocatedBridge.allocated_suffix_equivalent)))))))

theorem guard_cut_certificate : theoremCode (certificate guard_cut) =
    imp guard.encode (existsCode 41 cutBody.encode) := certificate_correct guard_cut

theorem guard_suffix_certificate : theoremCode (certificate guard_suffix) =
    imp guard.encode (imp cutBody.encode
      (imp PAtoCompactMemberCutRawTargetIntro.targetSuffix.encode (PASoundness.PAtoCompactTermTranslation.equivAt 100 34 38).encode)) :=
  certificate_correct guard_suffix
end PASoundness.PAtoCompactMemberChosenGuardInputs

#print axioms PASoundness.PAtoCompactMemberChosenGuardInputs.guard_cut
#print axioms PASoundness.PAtoCompactMemberChosenGuardInputs.guard_suffix
#print axioms PASoundness.PAtoCompactMemberChosenGuardInputs.guard_cut_certificate
#print axioms PASoundness.PAtoCompactMemberChosenGuardInputs.guard_suffix_certificate
