import PASoundness.PAtoCompactStagedEquivalenceAligned
import PASoundness.PAtoCompactFirstAdditionCutAllocation
import PASoundness.PAtoCompactDynamicTransitivityFinal

/-! Replace both operand-equivalence conjuncts of one actual addition witness
by transitivity, retaining its cut, suffix, filter and cut relation. -/
namespace PASoundness.PAtoCompactFirstAdditionOperandTransportPoint

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactStagedEquivalenceAlpha PASoundness.PAtoCompactStagedEquivalenceAligned
open PASoundness.PAtoCompactFirstAdditionCutAllocation PASoundness.PAtoCompactSeededSpanCutCandidate
open PASoundness.PAtoCompactFirstSpanPathOutside PASoundness.PAtoCompactDynamicTransitivityFinal

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guard : Formula := namedBoth (domainAt 100 29) (namedBoth (domainAt 100 27)
  (namedBoth (equivAt 100 29 28) (namedBoth (equivAt 100 27 1) allocatedBody)))
def transportedBody : Formula := namedBoth sourceRelation (namedBoth (rawStaged 29 40)
  (namedBoth PASoundness.PAtoCompactFirstSpanPathOutside.suffixFilter (rawStaged 27 31)))

private theorem old_cut_shape : PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences.firstEquivalence =
    rawStaged 28 40 := by decide
private theorem old_suffix_shape : PASoundness.PAtoCompactSuffixCleanWitness.suffixEquivalence =
    rawStaged 1 31 := by decide

/-- Both new operands are explicit candidates and explicitly isomorphic to
the old operands; the same cut and suffix witness are preserved. -/
def transport_operand_witness : KDerivation (imp guard.encode transportedBody.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hd29 : Context Γ (domainAt 100 29).encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hd27 : Context Γ (domainAt 100 27).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have heA : Context Γ (equivAt 100 29 28).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have heB : Context Γ (equivAt 100 27 1).encode := Context.conjunctionLeft hr
  have hb : Context Γ allocatedBody.encode := Context.conjunctionRight hr
  have hrel : Context Γ sourceRelation.encode := Context.conjunctionLeft hb
  have hr := Context.conjunctionRight hb
  have hcut0 : Context Γ PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences.firstEquivalence.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hfilter : Context Γ PASoundness.PAtoCompactFirstSpanPathOutside.suffixFilter.encode := Context.conjunctionLeft hr
  have hsuf0 : Context Γ PASoundness.PAtoCompactSuffixCleanWitness.suffixEquivalence.encode := Context.conjunctionRight hr
  have hcut : Context Γ (rawStaged 28 40).encode := by simpa only [old_cut_shape] using hcut0
  have hsuf : Context Γ (rawStaged 1 31).encode := by simpa only [old_suffix_shape] using hsuf0
  have hcutA : Context Γ (equivAt 100 28 40).encode := .mp hcut
    (.closed (staged_to_allocated 28 40 (by decide) (by decide) (by decide) (by decide) (by decide)))
  have hsufA : Context Γ (equivAt 100 1 31).encode := .mp hsuf
    (.closed (staged_to_allocated 1 31 (by decide) (by decide) (by decide) (by decide) (by decide)))
  have hnewCut : Context Γ (equivAt 100 29 40).encode :=
    .mp hcutA (.mp heA (.mp hd29 (.closed (dynamic_transitivity 100 29 28 40 (by decide) (by decide) (by decide)))))
  have hnewSuffix : Context Γ (equivAt 100 27 31).encode :=
    .mp hsufA (.mp heB (.mp hd27 (.closed (dynamic_transitivity 100 27 1 31 (by decide) (by decide) (by decide)))))
  have hcutRaw : Context Γ (rawStaged 29 40).encode := .mp hnewCut
    (.closed (allocated_to_staged 29 40 (by decide) (by decide) (by decide) (by decide) (by decide)))
  have hsufRaw : Context Γ (rawStaged 27 31).encode := .mp hnewSuffix
    (.closed (allocated_to_staged 27 31 (by decide) (by decide) (by decide) (by decide) (by decide)))
  exact Context.conjunctionIntro hrel (Context.conjunctionIntro hcutRaw (Context.conjunctionIntro hfilter hsufRaw))

theorem transport_operand_witness_certificate : theoremCode (certificate transport_operand_witness) =
    imp guard.encode transportedBody.encode := certificate_correct transport_operand_witness

end PASoundness.PAtoCompactFirstAdditionOperandTransportPoint

#print axioms PASoundness.PAtoCompactFirstAdditionOperandTransportPoint.guard
#print axioms PASoundness.PAtoCompactFirstAdditionOperandTransportPoint.transportedBody
#print axioms PASoundness.PAtoCompactFirstAdditionOperandTransportPoint.transport_operand_witness
#print axioms PASoundness.PAtoCompactFirstAdditionOperandTransportPoint.transport_operand_witness_certificate
