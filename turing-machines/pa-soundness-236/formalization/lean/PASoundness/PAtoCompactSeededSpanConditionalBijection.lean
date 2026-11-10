import PASoundness.PAtoCompactSeededSpanForwardCoverage
import PASoundness.PAtoCompactSeededSpanReverseCoverage
import PASoundness.PAtoCompactSeededSpanGlobalUniqueness
import PASoundness.PAtoCompactSeededSpanUniquenessFamilies
import PASoundness.PAtoCompactForwardBijectionFromCoverage
import PASoundness.PAtoCompactReverseBijectionFromCoverage

/-! Assemble the literal graph9 bijection from the proved conditional forward
and reverse coverages and quantified uniqueness, under a guard retaining the
actual full-prefix invariant, seed/suffix graphs, candidates, filters and cut
relations. This does not construct the graph or prove addition congruence. -/
namespace PASoundness.PAtoCompactSeededSpanConditionalBijection

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactScopedActiveReplace

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def fullUniqueGuard : Formula := replace 10 1 PASoundness.PAtoCompactSeededSpanGlobalUniqueness.globalGuard
def guard : Formula := namedBoth PASoundness.PAtoCompactSeededSpanForwardCoverage.globalGuard
  (namedBoth PASoundness.PAtoCompactSeededSpanReverseCoverage.globalGuard fullUniqueGuard)
def targetBijection : Formula := replace 6 9 (replace 1 8 bijectionFormula)

private def uniqueFrame : Formula := .imp PASoundness.PAtoCompactSeededSpanGlobalUniqueness.globalGuard
  PASoundness.PAtoCompactSeededSpanGlobalUniqueness.quantifiedUniqueness
private theorem unique_frame_alignment : replace 10 1 uniqueFrame = .imp fullUniqueGuard
    PASoundness.PAtoCompactSeededSpanGlobalUniqueness.quantifiedUniqueness := by decide
private theorem target_shape : targetBijection = namedBoth
    PASoundness.PAtoCompactConditionalTransitivityForwardClause.forwardClause
    PASoundness.PAtoCompactConditionalTransitivityReverseClause.rightClause := by decide

private def full_unique : KDerivation (imp fullUniqueGuard.encode
    PASoundness.PAtoCompactSeededSpanGlobalUniqueness.quantifiedUniqueness.encode) := by
  have hbase : KDerivation uniqueFrame.encode := by
    simpa only [uniqueFrame,Formula.encode] using PASoundness.PAtoCompactSeededSpanGlobalUniqueness.global_uniqueness_lift
  have h := replace_derivation 10 1 uniqueFrame (by decide) (by decide) hbase
  rw [unique_frame_alignment] at h
  exact h

/-- The same graph9 satisfies the exact source/target bijection formula under
the three displayed conditional guards. -/
def conditional_bijection : KDerivation (imp guard.encode targetBijection.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hfGuard : Context Γ PASoundness.PAtoCompactSeededSpanForwardCoverage.globalGuard.encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hrGuard : Context Γ PASoundness.PAtoCompactSeededSpanReverseCoverage.globalGuard.encode := Context.conjunctionLeft hr
  have huGuard : Context Γ fullUniqueGuard.encode := Context.conjunctionRight hr
  have hf : Context Γ PASoundness.PAtoCompactSeededSpanForwardCoverage.forwardCoverage.encode :=
    .mp hfGuard (.closed PASoundness.PAtoCompactSeededSpanForwardCoverage.forward_coverage)
  have hrev : Context Γ PASoundness.PAtoCompactSeededSpanReverseCoverage.reverseCoverage.encode :=
    .mp hrGuard (.closed PASoundness.PAtoCompactSeededSpanReverseCoverage.reverse_coverage)
  have hu : Context Γ PASoundness.PAtoCompactSeededSpanGlobalUniqueness.quantifiedUniqueness.encode :=
    .mp huGuard (.closed full_unique)
  have htf : Context Γ PASoundness.PAtoCompactConditionalTransitivityTargetAll.targetFamily.encode :=
    .mp hu (.closed PASoundness.PAtoCompactSeededSpanUniquenessFamilies.target_family_from_uniqueness)
  have hsf : Context Γ PASoundness.PAtoCompactConditionalTransitivitySourceAll.family.encode :=
    .mp hu (.closed PASoundness.PAtoCompactSeededSpanUniquenessFamilies.source_family_from_uniqueness)
  have hfg : Context Γ PASoundness.PAtoCompactForwardBijectionFromCoverage.guard.encode :=
    Context.conjunctionIntro hf htf
  have hrg : Context Γ PASoundness.PAtoCompactReverseBijectionFromCoverage.guard.encode :=
    Context.conjunctionIntro hrev hsf
  have hforward : Context Γ PASoundness.PAtoCompactConditionalTransitivityForwardClause.forwardClause.encode :=
    .mp hfg (.closed PASoundness.PAtoCompactForwardBijectionFromCoverage.forward_bijection_from_coverage)
  have hreverse : Context Γ PASoundness.PAtoCompactConditionalTransitivityReverseClause.rightClause.encode :=
    .mp hrg (.closed PASoundness.PAtoCompactReverseBijectionFromCoverage.reverse_bijection_from_coverage)
  rw [target_shape]
  exact Context.conjunctionIntro hforward hreverse

theorem conditional_bijection_certificate : theoremCode (certificate conditional_bijection) =
    imp guard.encode targetBijection.encode := certificate_correct conditional_bijection

end PASoundness.PAtoCompactSeededSpanConditionalBijection

#print axioms PASoundness.PAtoCompactSeededSpanConditionalBijection.fullUniqueGuard
#print axioms PASoundness.PAtoCompactSeededSpanConditionalBijection.guard
#print axioms PASoundness.PAtoCompactSeededSpanConditionalBijection.targetBijection
#print axioms PASoundness.PAtoCompactSeededSpanConditionalBijection.conditional_bijection
#print axioms PASoundness.PAtoCompactSeededSpanConditionalBijection.conditional_bijection_certificate
