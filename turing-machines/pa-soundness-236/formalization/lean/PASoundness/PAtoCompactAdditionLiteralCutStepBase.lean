import PASoundness.PAtoCompactAdditionSuccessorLocalStep

/-! Retaining one actual cut in a K addition successor construction. The
input cut may be any object satisfying the displayed cut alternative; this
module constructs a new suffix, not the addition totality induction. It does
not assume transitivity of the relative suffix or use semantic soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionLiteralCutStepBase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactAdditionRightContext
open PASoundness.PAtoCompactAdditionSuccessorEquivStep PASoundness.PAtoCompactAdditionEliminateCleanOldGraph
open PASoundness.PAtoCompactAdditionSuccessorLocalStep PASoundness.PAtoCompactAdditionCandidateCutStep
open PASoundness.PAtoCompactAdditionDomainTransitivity
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The new result's filter relative to the same cut name 33. -/
def newFilter : Formula := .all 35 (namedFilterBody 45 40 35 (Formula.member 33 35).not)
/-- The new suffix has exactly that filter and is equivalent to the successor
of the old second input. -/
def newSuffix : Formula := .ex 40 (namedBoth newFilter (equivAt 38 40))
/-- The displayed inputs retain the same cut name in the conclusion. -/
def baseStep : Formula := .imp fixedAssumptions (.imp oldCut (.imp oldFilter
  (.imp oldRightEquiv (namedBoth (.member 45 33) newSuffix))))

private def witness_projection : KDerivation (imp
    (namedBoth suffixWitness (equivAt 38 40)).encode
    (namedBoth newFilter (equivAt 38 40)).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  have h : Context [(namedBoth suffixWitness (equivAt 38 40)).encode]
      (namedBoth suffixWitness (equivAt 38 40)).encode := .head _ _
  have hfilter := Context.conjunctionRight (Context.conjunctionLeft h)
  have hequiv := Context.conjunctionRight h
  exact Context.conjunctionIntro hfilter hequiv

/-- From the old cut alternative, old suffix filter and equivalence, and
candidate/raw-successor hypotheses, the same cut belongs to the new result
and admits a new suffix equivalent to the successor of the second input. -/
def base_step : KDerivation baseStep.encode := by
  have hmap : KDerivation (imp suffixAndEquiv.encode newSuffix.encode) := by
    change KDerivation (imp (existsCode 40 (namedBoth suffixWitness (equivAt 38 40)).encode)
      (existsCode 40 (namedBoth newFilter (equivAt 38 40)).encode))
    exact existsCongr 40 witness_projection
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldRightEquiv.encode,oldFilter.encode,oldCut.encode,fixedAssumptions.encode]
  have he : Context Γ oldRightEquiv.encode := .head _ _
  have hf : Context Γ oldFilter.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ oldCut.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ fixedAssumptions.encode := .hypothesis (by simp [Γ])
  have hD1 : Context Γ (domainAt 100 31).encode := Context.conjunctionLeft hp
  have hr := Context.conjunctionRight hp
  have hD2 : Context Γ (domainAt 100 32).encode := Context.conjunctionLeft hr
  have hs : Context Γ (successorCode 31 38 39) := Context.conjunctionLeft (Context.conjunctionRight hr)
  have ht : Context Γ (successorCode 32 45 39) := Context.conjunctionRight (Context.conjunctionRight hr)
  have hcut : Context Γ (both (neg (member 33 32)) (member 45 33)) :=
    .mp ht (.mp hc (.mp hD2 (.closed candidate_cut_step)))
  have hsrc : Context Γ (transitiveCode 31 37 38) := .mp hD1 (.closed source_transitive)
  have hresult : Context Γ (transitiveCode 32 37 38) := .mp hD2 (.closed result_transitive)
  have hgraphFree : Context Γ graphFreeAssumptions.encode := by
    exact Context.conjunctionIntro hf (Context.conjunctionIntro hs (Context.conjunctionIntro hsrc hresult))
  have hex : Context Γ suffixAndEquiv.encode :=
    .mp ht (.mp (Context.conjunctionLeft hcut)
      (.mp hgraphFree (.mp he (.closed eliminate_old_graph))))
  exact Context.conjunctionIntro (Context.conjunctionRight hcut) (.mp hex (.closed hmap))

theorem base_step_certificate : theoremCode (certificate base_step) = baseStep.encode :=
  certificate_correct base_step
end PASoundness.PAtoCompactAdditionLiteralCutStepBase
#print axioms PASoundness.PAtoCompactAdditionLiteralCutStepBase.base_step
#print axioms PASoundness.PAtoCompactAdditionLiteralCutStepBase.base_step_certificate
