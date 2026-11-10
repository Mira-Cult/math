import PASoundness.PAtoCompactSeededSpanConditionalMatrix
import PASoundness.PAtoCompactFirstSuffixOrderWiden
import PASoundness.PAtoCompactSecondSuffixOrderWiden
import PASoundness.PAtoCompactSeededSpanOrderFreshening

/-! Replace the two explicit whole-domain order inputs of the conditional
graph9 matrix with actual suffix-order clauses and the already supplied clean
graphs. All graph/seed/candidate/filter/cut hypotheses remain explicit; this
does not construct graph9 or prove general addition congruence. -/
namespace PASoundness.PAtoCompactSeededSpanMatrixFromSuffixOrders

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage PASoundness.PAtoCompactSeededSpanSeedOrder
open PASoundness.PAtoCompactSeededSpanCleanEndpoints PASoundness.PAtoCompactFirstSpanPathOutside
open PASoundness.PAtoCompactFirstSpanTargetOutside PASoundness.PAtoCompactSuffixCleanGraphGuard

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def baseGuard : Formula := namedBoth fullSpan (namedBoth (namedCandidate 0)
  (namedBoth (namedCandidate 8) (namedBoth (namedCandidate 40) (namedBoth (namedCandidate 41)
    (namedBoth (namedEither (.equal 40 0) (.member 0 40))
      (namedBoth (namedEither (.equal 41 8) (.member 8 41))
        (namedBoth outsideGuard (namedBoth targetGuard (namedBoth seedClean seedOrder)))))))))
def guard : Formula := namedBoth PASoundness.PAtoCompactSeededSpanConditionalBijection.guard
  (namedBoth baseGuard (namedBoth PASoundness.PAtoCompactFirstSuffixOrderWiden.suffixOrder
    PASoundness.PAtoCompactSecondSuffixOrderWiden.suffixOrder))

/-- The literal same-graph isomorphism matrix follows when the two source
order clauses are supplied on their suffixes and both graphs are clean. -/
def matrix_from_suffix_orders : KDerivation (imp guard.encode
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
  have hseedClean : Context Γ seedClean.encode := Context.conjunctionLeft hr
  have hseedOrder : Context Γ seedOrder.encode := Context.conjunctionRight hr
  have hclean1 : Context Γ storedClean.encode := Context.conjunctionLeft hsource
  have hclean2 : Context Γ targetClean.encode := Context.conjunctionLeft htarget
  have hw1 : Context Γ PASoundness.PAtoCompactFirstSuffixOrderWiden.wholeOrder.encode :=
    .mp hclean1 (.mp hs1 (.closed PASoundness.PAtoCompactFirstSuffixOrderWiden.first_suffix_order_widen))
  have hw2 : Context Γ PASoundness.PAtoCompactSecondSuffixOrderWiden.wholeOrder.encode :=
    .mp hclean2 (.mp hs2 (.closed PASoundness.PAtoCompactSecondSuffixOrderWiden.second_suffix_order_widen))
  have hf1 : Context Γ PASoundness.PAtoCompactSeededSpanSelectedPathOrder.firstOrder.encode :=
    .mp hw1 (.closed PASoundness.PAtoCompactSeededSpanOrderFreshening.first_order_fresh)
  have hf2 : Context Γ PASoundness.PAtoCompactSeededSpanSelectedPathOrder.secondOrder.encode :=
    .mp hw2 (.closed PASoundness.PAtoCompactSeededSpanOrderFreshening.second_order_fresh)
  have horder : Context Γ PASoundness.PAtoCompactSeededSpanConditionalMatrix.fullOrderGuard.encode :=
    Context.conjunctionIntro hspan (Context.conjunctionIntro hc0 (Context.conjunctionIntro hc8
      (Context.conjunctionIntro hc40 (Context.conjunctionIntro hc41 (Context.conjunctionIntro hrel0
        (Context.conjunctionIntro hrel8 (Context.conjunctionIntro hsource (Context.conjunctionIntro htarget
          (Context.conjunctionIntro hseedClean (Context.conjunctionIntro hseedOrder (Context.conjunctionIntro hf1 hf2)))))))))))
  have hguard : Context Γ PASoundness.PAtoCompactSeededSpanConditionalMatrix.guard.encode :=
    Context.conjunctionIntro hbij horder
  exact .mp hguard (.closed PASoundness.PAtoCompactSeededSpanConditionalMatrix.conditional_isomorphism_matrix)

theorem matrix_from_suffix_orders_certificate : theoremCode (certificate matrix_from_suffix_orders) =
    imp guard.encode PASoundness.PAtoCompactSeededSpanConditionalMatrix.targetMatrix.encode :=
  certificate_correct matrix_from_suffix_orders

end PASoundness.PAtoCompactSeededSpanMatrixFromSuffixOrders

#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromSuffixOrders.baseGuard
#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromSuffixOrders.guard
#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromSuffixOrders.matrix_from_suffix_orders
#print axioms PASoundness.PAtoCompactSeededSpanMatrixFromSuffixOrders.matrix_from_suffix_orders_certificate
