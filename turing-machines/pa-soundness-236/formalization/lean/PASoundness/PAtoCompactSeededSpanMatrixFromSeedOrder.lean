import PASoundness.PAtoCompactSeededSpanMatrixFromSuffixOrders

/-! Use the ordinary supplied seed-order clause in the conditional matrix
theorem. The graph, candidate, cut, filter and suffix-order hypotheses remain
explicit; no graph existence or general addition congruence is claimed. -/
namespace PASoundness.PAtoCompactSeededSpanMatrixFromSeedOrder

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage PASoundness.PAtoCompactSeededSpanSeedOrder
open PASoundness.PAtoCompactSeededSpanCleanEndpoints PASoundness.PAtoCompactFirstSpanPathOutside
open PASoundness.PAtoCompactFirstSpanTargetOutside PASoundness.PAtoCompactSeededSpanOrderFreshening

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def baseGuard : Formula := namedBoth fullSpan (namedBoth (namedCandidate 0)
  (namedBoth (namedCandidate 8) (namedBoth (namedCandidate 40) (namedBoth (namedCandidate 41)
    (namedBoth (namedEither (.equal 40 0) (.member 0 40))
      (namedBoth (namedEither (.equal 41 8) (.member 8 41))
        (namedBoth outsideGuard (namedBoth targetGuard (namedBoth seedClean seedOriginal)))))))))

def guard : Formula := namedBoth PASoundness.PAtoCompactSeededSpanConditionalBijection.guard
  (namedBoth baseGuard (namedBoth PASoundness.PAtoCompactFirstSuffixOrderWiden.suffixOrder
    PASoundness.PAtoCompactSecondSuffixOrderWiden.suffixOrder))

/-- Freshen the supplied seed order and retain every other guard unchanged. -/
def matrix_from_seed_order : KDerivation (imp guard.encode
    PASoundness.PAtoCompactSeededSpanConditionalMatrix.targetMatrix.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hbij : Context Γ PASoundness.PAtoCompactSeededSpanConditionalBijection.guard.encode := Context.conjunctionLeft hg
  have htail := Context.conjunctionRight hg
  have hb : Context Γ baseGuard.encode := Context.conjunctionLeft htail
  have horders := Context.conjunctionRight htail
  have hs1 : Context Γ PASoundness.PAtoCompactFirstSuffixOrderWiden.suffixOrder.encode := Context.conjunctionLeft horders
  have hs2 : Context Γ PASoundness.PAtoCompactSecondSuffixOrderWiden.suffixOrder.encode := Context.conjunctionRight horders
  have hspan : Context Γ fullSpan.encode := Context.conjunctionLeft hb
  have hr := Context.conjunctionRight hb
  have hc0 : Context Γ (namedCandidate 0).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hc8 : Context Γ (namedCandidate 8).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hc40 : Context Γ (namedCandidate 40).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hc41 : Context Γ (namedCandidate 41).encode := Context.conjunctionLeft hr
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
  have horiginal : Context Γ seedOriginal.encode := Context.conjunctionRight hr
  have hfresh : Context Γ seedOrder.encode := .mp horiginal (.closed seed_order_fresh)
  have hbase : Context Γ PASoundness.PAtoCompactSeededSpanMatrixFromSuffixOrders.baseGuard.encode :=
    Context.conjunctionIntro hspan (Context.conjunctionIntro hc0 (Context.conjunctionIntro hc8
      (Context.conjunctionIntro hc40 (Context.conjunctionIntro hc41 (Context.conjunctionIntro hrel0
        (Context.conjunctionIntro hrel8 (Context.conjunctionIntro hsource (Context.conjunctionIntro htarget
          (Context.conjunctionIntro hclean hfresh)))))))))
  have hguard : Context Γ PASoundness.PAtoCompactSeededSpanMatrixFromSuffixOrders.guard.encode :=
    Context.conjunctionIntro hbij (Context.conjunctionIntro hbase (Context.conjunctionIntro hs1 hs2))
  exact .mp hguard (.closed PASoundness.PAtoCompactSeededSpanMatrixFromSuffixOrders.matrix_from_suffix_orders)

theorem matrix_from_seed_order_certificate : theoremCode (certificate matrix_from_seed_order) =
    imp guard.encode PASoundness.PAtoCompactSeededSpanConditionalMatrix.targetMatrix.encode :=
  certificate_correct matrix_from_seed_order

end PASoundness.PAtoCompactSeededSpanMatrixFromSeedOrder

#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromSeedOrder.baseGuard
#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromSeedOrder.guard
#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromSeedOrder.matrix_from_seed_order
#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromSeedOrder.matrix_from_seed_order_certificate
