import PASoundness.PAtoCompactSeededSpanMatrixFromSeedOrder

/-! Consolidate the repeated assumptions in the conditional same-graph
matrix theorem. Every displayed graph, order, candidate, cut and filter
premise remains explicit. -/
namespace PASoundness.PAtoCompactSeededSpanMatrixConsolidated

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage PASoundness.PAtoCompactSeededSpanSeedSourceUnique
open PASoundness.PAtoCompactSeededSpanCleanEndpoints PASoundness.PAtoCompactFirstSpanPathOutside
open PASoundness.PAtoCompactFirstSpanTargetOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guard : Formula := namedBoth seedBijection (namedBoth firstBijection (namedBoth secondBijection
  (namedBoth PASoundness.PAtoCompactSeededSpanMatrixFromSeedOrder.baseGuard
    (namedBoth PASoundness.PAtoCompactFirstSuffixOrderWiden.suffixOrder
      PASoundness.PAtoCompactSecondSuffixOrderWiden.suffixOrder))))

/-- Assemble the three coverage/uniqueness guards from their shared inputs. -/
def matrix_from_consolidated_guard : KDerivation (imp guard.encode
    PASoundness.PAtoCompactSeededSpanConditionalMatrix.targetMatrix.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hseed : Context Γ seedBijection.encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hf : Context Γ firstBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hs : Context Γ secondBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hb : Context Γ PASoundness.PAtoCompactSeededSpanMatrixFromSeedOrder.baseGuard.encode := Context.conjunctionLeft hr
  have ho := Context.conjunctionRight hr
  have hspan : Context Γ fullSpan.encode := Context.conjunctionLeft hb
  have hr := Context.conjunctionRight hb
  have hc0 : Context Γ (namedCandidate 0).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hc8 : Context Γ (namedCandidate 8).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hr := Context.conjunctionRight hr
  have hr := Context.conjunctionRight hr
  have hrel0 : Context Γ (either (equal 40 0) (member 0 40)) := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hrel8 : Context Γ (either (equal 41 8) (member 8 41)) := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hsource : Context Γ outsideGuard.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have htarget : Context Γ targetGuard.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hclean : Context Γ seedClean.encode := Context.conjunctionLeft hr
  have hfilter1 : Context Γ suffixFilter.encode := Context.conjunctionRight hsource
  have hfilter2 : Context Γ targetFilter.encode := Context.conjunctionRight htarget
  have hforward : Context Γ PASoundness.PAtoCompactSeededSpanForwardCoverage.globalGuard.encode :=
    Context.conjunctionIntro hspan (Context.conjunctionIntro hseed (Context.conjunctionIntro hc8
      (Context.conjunctionIntro hrel8 (Context.conjunctionIntro hf (Context.conjunctionIntro hs
        (Context.conjunctionIntro hfilter1 hfilter2))))))
  have hreverse : Context Γ PASoundness.PAtoCompactSeededSpanReverseCoverage.globalGuard.encode :=
    Context.conjunctionIntro hspan (Context.conjunctionIntro hseed (Context.conjunctionIntro hc0
      (Context.conjunctionIntro hrel0 (Context.conjunctionIntro hf (Context.conjunctionIntro hs
        (Context.conjunctionIntro hfilter1 hfilter2))))))
  have hunique : Context Γ PASoundness.PAtoCompactSeededSpanConditionalBijection.fullUniqueGuard.encode :=
    Context.conjunctionIntro hseed (Context.conjunctionIntro hspan (Context.conjunctionIntro hclean
      (Context.conjunctionIntro hsource (Context.conjunctionIntro htarget (Context.conjunctionIntro hf hs)))))
  have hbij : Context Γ PASoundness.PAtoCompactSeededSpanConditionalBijection.guard.encode :=
    Context.conjunctionIntro hforward (Context.conjunctionIntro hreverse hunique)
  have hguard : Context Γ PASoundness.PAtoCompactSeededSpanMatrixFromSeedOrder.guard.encode :=
    Context.conjunctionIntro hbij (Context.conjunctionIntro hb ho)
  exact .mp hguard (.closed PASoundness.PAtoCompactSeededSpanMatrixFromSeedOrder.matrix_from_seed_order)

theorem matrix_from_consolidated_guard_certificate : theoremCode (certificate matrix_from_consolidated_guard) =
    imp guard.encode PASoundness.PAtoCompactSeededSpanConditionalMatrix.targetMatrix.encode :=
  certificate_correct matrix_from_consolidated_guard

end PASoundness.PAtoCompactSeededSpanMatrixConsolidated

#print axioms PASoundness.PAtoCompactSeededSpanMatrixConsolidated.guard
#print axioms PASoundness.PAtoCompactSeededSpanMatrixConsolidated.matrix_from_consolidated_guard
#print axioms PASoundness.PAtoCompactSeededSpanMatrixConsolidated.matrix_from_consolidated_guard_certificate
