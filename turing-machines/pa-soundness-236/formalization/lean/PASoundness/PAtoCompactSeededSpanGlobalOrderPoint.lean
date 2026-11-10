import PASoundness.PAtoCompactSeededSpanMixedCandidates
import PASoundness.PAtoCompactSeededSpanCleanEndpoints
import PASoundness.PAtoCompactPartialCompositionAtSource

/-! Pointwise graph order from a single fixed global named guard. The point
guard itself supplies the actual whole memberships and two graph edges. All
candidate, cut, clean-filter, seed-order and source-order premises remain
explicit in the global guard. -/
namespace PASoundness.PAtoCompactSeededSpanGlobalOrderPoint

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPartialCompositionAtSource PASoundness.PAtoCompactSeededSpanBase
open PASoundness.PAtoCompactSeededSpanOrderCases PASoundness.PAtoCompactSeededSpanMixedOrder
open PASoundness.PAtoCompactSeededSpanPointOrder PASoundness.PAtoCompactSeededSpanSeedOrder
open PASoundness.PAtoCompactSeededSpanPathOrder PASoundness.PAtoCompactSeededSpanSelectedPathOrder
open PASoundness.PAtoCompactSeededSpanCleanEndpoints PASoundness.PAtoCompactSeededSpanMixedCandidates
open PASoundness.PAtoCompactSeededSpanMixedGuards PASoundness.PAtoCompactMixedCandidateFixedAlignment
open PASoundness.PAtoCompactFirstSpanPathOutside PASoundness.PAtoCompactFirstSpanTargetOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def globalGuard : Formula := namedBoth seededSpan (namedBoth (namedCandidate 0)
  (namedBoth (namedCandidate 8) (namedBoth (namedCandidate 40) (namedBoth (namedCandidate 41)
    (namedBoth (namedEither (.equal 40 0) (.member 0 40))
      (namedBoth (namedEither (.equal 41 8) (.member 8 41))
        (namedBoth outsideGuard (namedBoth targetGuard (namedBoth seedClean
          (namedBoth seedOrder (namedBoth firstOrder secondOrder)))))))))))

def pointGuard : Formula := namedBoth (.member 0 2) (namedBoth (.member 0 26)
  (namedBoth (.member 8 3) (namedBoth (.member 8 27)
    (namedBoth (graphFormula 9 2 3) (graphFormula 9 26 27)))))
def pointComparison : Formula := namedBoth (.imp (.member 26 2) (.member 27 3))
  (.imp (.member 27 3) (.member 26 2))
def pointClause : Formula := .imp pointGuard pointComparison

/-- The exact point comparison follows from the single fixed guard and the
point clause's six actual domain and graph hypotheses. -/
def global_order_point : KDerivation (imp globalGuard.encode pointClause.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [pointGuard.encode,globalGuard.encode]
  have hp : Context Γ pointGuard.encode := .head _ _
  have hg : Context Γ globalGuard.encode := .hypothesis (by simp [Γ])
  have hi : Context Γ seededSpan.encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hsc : Context Γ sourceCandidate := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have htc : Context Γ targetCandidate := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hscc : Context Γ sourceCutCandidate := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have htcc : Context Γ targetCutCandidate := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hsr : Context Γ sourceCutRelation := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have htr : Context Γ targetCutRelation := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hso : Context Γ outsideGuard.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hto : Context Γ targetGuard.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hclean : Context Γ seedClean.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hseedOrder : Context Γ seedOrder.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hfirst : Context Γ firstOrder.encode := Context.conjunctionLeft hr
  have hsecond : Context Γ secondOrder.encode := Context.conjunctionRight hr
  have hm02 : Context Γ (member 0 2) := Context.conjunctionLeft hp
  have hp := Context.conjunctionRight hp
  have hm026 : Context Γ (member 0 26) := Context.conjunctionLeft hp
  have hp := Context.conjunctionRight hp
  have hm83 : Context Γ (member 8 3) := Context.conjunctionLeft hp
  have hp := Context.conjunctionRight hp
  have hm827 : Context Γ (member 8 27) := Context.conjunctionLeft hp
  have hp := Context.conjunctionRight hp
  have he1 : Context Γ (graphFormula 9 2 3).encode := Context.conjunctionLeft hp
  have he2 : Context Γ (graphFormula 9 26 27).encode := Context.conjunctionRight hp
  have hend : Context Γ seedEndpoints := .mp hclean (.closed seed_endpoints_from_clean)
  have horder : Context Γ orderGuard.encode := Context.conjunctionIntro hfirst
    (Context.conjunctionIntro hsecond (Context.conjunctionIntro hm02
      (Context.conjunctionIntro hm026 (Context.conjunctionIntro hm83 hm827))))
  have hmixed : Context Γ (mixedPremises 40 41) := .mp horder (.mp hend (.mp hto (.mp hso
    (.mp htr (.mp hsr (.mp htcc (.mp hscc (.mp htc (.mp hsc (.closed mixed_guards_from_candidates))))))))))
  exact .mp he2 (.mp he1 (.mp horder (.mp hend (.mp hseedOrder (.mp hmixed
    (.mp hi (.closed seeded_span_point_order)))))))

theorem global_order_point_certificate : theoremCode (certificate global_order_point) =
    imp globalGuard.encode pointClause.encode := certificate_correct global_order_point

end PASoundness.PAtoCompactSeededSpanGlobalOrderPoint

#print axioms PASoundness.PAtoCompactSeededSpanGlobalOrderPoint.globalGuard
#print axioms PASoundness.PAtoCompactSeededSpanGlobalOrderPoint.pointGuard
#print axioms PASoundness.PAtoCompactSeededSpanGlobalOrderPoint.pointComparison
#print axioms PASoundness.PAtoCompactSeededSpanGlobalOrderPoint.pointClause
#print axioms PASoundness.PAtoCompactSeededSpanGlobalOrderPoint.global_order_point
#print axioms PASoundness.PAtoCompactSeededSpanGlobalOrderPoint.global_order_point_certificate
