import PASoundness.PAtoCompactSeededSpanMatrixFromSuffixGraphs
import PASoundness.PAtoCompactSeededSpanCutCandidate

/-! Supply both cut-candidate premises from the stated whole candidates and
their equal-or-member cut relations. All graph, order and filter assumptions
remain explicit. -/
namespace PASoundness.PAtoCompactSeededSpanMatrixFromWholeCandidates

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage PASoundness.PAtoCompactSeededSpanSeedSourceUnique
open PASoundness.PAtoCompactSeededSpanCleanEndpoints PASoundness.PAtoCompactFirstSpanPathOutside
open PASoundness.PAtoCompactFirstSpanTargetOutside PASoundness.PAtoCompactSeededSpanOrderFreshening
open PASoundness.PAtoCompactSeededSpanCutCandidate

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def fixedBase : Formula := namedBoth (namedCandidate 0) (namedBoth (namedCandidate 8)
  (namedBoth sourceRelation (namedBoth targetRelation
    (namedBoth outsideGuard (namedBoth targetGuard (namedBoth seedClean seedOriginal))))))
def guard : Formula := namedBoth (namedCandidate 1) (namedBoth seedBijection
  (namedBoth firstBijection (namedBoth secondBijection
    (namedBoth fixedBase (namedBoth PASoundness.PAtoCompactFirstSuffixOrderWiden.suffixOrder
      PASoundness.PAtoCompactSecondSuffixOrderWiden.suffixOrder)))))

/-- The output matrix graph needs candidate wholes and the two cut relations;
the literal cut-candidate codes are obtained in K. -/
def matrix_from_whole_candidates : KDerivation (imp guard.encode
    PASoundness.PAtoCompactSeededSpanMatrixWitness.output.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hc1 : Context Γ (namedCandidate 1).encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hseed : Context Γ seedBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hb1 : Context Γ firstBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hb2 : Context Γ secondBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hb : Context Γ fixedBase.encode := Context.conjunctionLeft hr
  have ho := Context.conjunctionRight hr
  have hc0 : Context Γ (namedCandidate 0).encode := Context.conjunctionLeft hb
  have hr := Context.conjunctionRight hb
  have hc8 : Context Γ (namedCandidate 8).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hrel0 : Context Γ sourceRelation.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hrel8 : Context Γ targetRelation.encode := Context.conjunctionLeft hr
  have htail := Context.conjunctionRight hr
  have hc40 : Context Γ (namedCandidate 40).encode := .mp hrel0 (.mp hc0 (.closed source_cut_candidate))
  have hc41 : Context Γ (namedCandidate 41).encode := .mp hrel8 (.mp hc8 (.closed target_cut_candidate))
  have hbase : Context Γ PASoundness.PAtoCompactSeededSpanMatrixWitness.fixedBase.encode :=
    Context.conjunctionIntro hc0 (Context.conjunctionIntro hc8 (Context.conjunctionIntro hc40
      (Context.conjunctionIntro hc41 (Context.conjunctionIntro hrel0 (Context.conjunctionIntro hrel8 htail)))))
  have hguard : Context Γ PASoundness.PAtoCompactSeededSpanMatrixFromSuffixGraphs.guard.encode :=
    Context.conjunctionIntro hc1 (Context.conjunctionIntro hseed (Context.conjunctionIntro hb1
      (Context.conjunctionIntro hb2 (Context.conjunctionIntro hbase ho))))
  exact .mp hguard (.closed PASoundness.PAtoCompactSeededSpanMatrixFromSuffixGraphs.matrix_from_suffix_graphs)

theorem matrix_from_whole_candidates_certificate : theoremCode (certificate matrix_from_whole_candidates) =
    imp guard.encode PASoundness.PAtoCompactSeededSpanMatrixWitness.output.encode :=
  certificate_correct matrix_from_whole_candidates

end PASoundness.PAtoCompactSeededSpanMatrixFromWholeCandidates

#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromWholeCandidates.fixedBase
#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromWholeCandidates.guard
#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromWholeCandidates.matrix_from_whole_candidates
#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromWholeCandidates.matrix_from_whole_candidates_certificate
