import PASoundness.PAtoCompactSeededSpanMatrixFromCutEquivalence
import PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences

/-! Replace the cut-to-cut equivalence premise by two supplied cut
isomorphisms from one candidate common source. -/
namespace PASoundness.PAtoCompactSeededSpanMatrixFromCommonCutSource

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage PASoundness.PAtoCompactSeededSpanCleanSeedWitness
open PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guard : Formula := namedBoth PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences.guard
  (namedBoth (namedCandidate 1) (namedBoth firstBijection (namedBoth secondBijection
    (namedBoth PASoundness.PAtoCompactSeededSpanMatrixFromCutEquivalence.fixedBase
      (namedBoth PASoundness.PAtoCompactFirstSuffixOrderWiden.suffixOrder
        PASoundness.PAtoCompactSecondSuffixOrderWiden.suffixOrder)))))

/-- The actual common-source isomorphisms supply the cut equivalence; all
other graph, order, candidate and filter assumptions remain explicit. -/
def matrix_from_common_cut_source : KDerivation (imp guard.encode
    PASoundness.PAtoCompactSeededSpanMatrixWitness.output.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have heqGuard : Context Γ PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences.guard.encode :=
    Context.conjunctionLeft hg
  have htail := Context.conjunctionRight hg
  have hc1 : Context Γ (namedCandidate 1).encode := Context.conjunctionLeft htail
  have hrest := Context.conjunctionRight htail
  have heq : Context Γ seedEquivalence.encode := .mp heqGuard (.closed cut_equivalence_from_equivalences)
  have hguard : Context Γ PASoundness.PAtoCompactSeededSpanMatrixFromCutEquivalence.guard.encode :=
    Context.conjunctionIntro hc1 (Context.conjunctionIntro heq hrest)
  exact .mp hguard (.closed PASoundness.PAtoCompactSeededSpanMatrixFromCutEquivalence.matrix_from_cut_equivalence)

theorem matrix_from_common_cut_source_certificate : theoremCode (certificate matrix_from_common_cut_source) =
    imp guard.encode PASoundness.PAtoCompactSeededSpanMatrixWitness.output.encode :=
  certificate_correct matrix_from_common_cut_source

end PASoundness.PAtoCompactSeededSpanMatrixFromCommonCutSource

#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromCommonCutSource.guard
#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromCommonCutSource.matrix_from_common_cut_source
#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromCommonCutSource.matrix_from_common_cut_source_certificate
