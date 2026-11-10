import PASoundness.PAtoCompactSeededSpanSuffixReverseCoverage
import PASoundness.PAtoCompactSeededSpanSeedReverseCoverage
import PASoundness.PAtoCompactSeededSpanSourceCutContained
import PASoundness.PAtoCompactTargetSuffixMembership

/-! Reverse coverage of graph9 under a fixed explicit guard. A whole-target
point is split on cut41 membership; the seed or target-suffix construction
produces an actual graph9 preimage in whole0. This establishes coverage only,
not uniqueness, forward coverage or a full graph bijection. -/
namespace PASoundness.PAtoCompactSeededSpanReverseCoverage

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactSeededSpanSeedSourceUnique PASoundness.PAtoCompactSeededSpanSuffixReverseCoverage
open PASoundness.PAtoCompactSeededSpanSourceCutContained PASoundness.PAtoCompactTargetSuffixMembership
open PASoundness.PAtoCompactFirstSpanPathOutside PASoundness.PAtoCompactFirstSpanTargetOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def globalGuard : Formula := namedBoth fullSpan (namedBoth seedBijection (namedBoth (namedCandidate 0)
  (namedBoth (namedEither (.equal 40 0) (.member 0 40)) (namedBoth firstBijection
    (namedBoth secondBijection (namedBoth suffixFilter targetFilter))))))
def output : Formula := PASoundness.PAtoCompactSeededSpanSuffixReverseCoverage.output
def point : Formula := .imp (.member 8 3) output
def reverseCoverage : Formula := .all 3 point

private def seedFrame : Formula := .imp PASoundness.PAtoCompactSeededSpanSeedReverseCoverage.guard
  PASoundness.PAtoCompactSeededSpanSeedReverseCoverage.output
private def seedFullGuard : Formula := namedBoth fullSpan (namedBoth seedBijection
  (namedBoth PASoundness.PAtoCompactSeededSpanSeedReverseCoverage.cutContained
    (namedBoth (.member 8 3) (.member 41 3))))
private theorem seed_frame_alignment : replace 10 1 seedFrame = .imp seedFullGuard output := by decide

private def full_seed_coverage : KDerivation (imp seedFullGuard.encode output.encode) := by
  have hbase : KDerivation seedFrame.encode := by
    simpa only [seedFrame,Formula.encode] using PASoundness.PAtoCompactSeededSpanSeedReverseCoverage.seed_reverse_coverage
  have h := replace_derivation 10 1 seedFrame (by decide) (by decide) hbase
  rw [seed_frame_alignment] at h
  exact h

/-- For a whole-target point, either its seed edge or its suffix path yields
an actual graph9 preimage in whole0 under the stated fixed global premises. -/
def reverse_coverage_point : KDerivation (imp globalGuard.encode point.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 8 3,globalGuard.encode]
  have hm : Context Γ (member 8 3) := .head _ _
  have hg : Context Γ globalGuard.encode := .hypothesis (by simp [Γ])
  have hspan : Context Γ fullSpan.encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hseed : Context Γ seedBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hcandidate : Context Γ (namedCandidate 0).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hrel : Context Γ (either (equal 40 0) (member 0 40)) := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hfirst : Context Γ firstBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hsecond : Context Γ secondBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hsourceFilter : Context Γ suffixFilter.encode := Context.conjunctionLeft hr
  have htargetFilter : Context Γ targetFilter.encode := Context.conjunctionRight hr
  have hcutGuard : Context Γ PASoundness.PAtoCompactSeededSpanSourceCutContained.guard.encode :=
    Context.conjunctionIntro hcandidate hrel
  have hcontained : Context Γ PASoundness.PAtoCompactSeededSpanSeedReverseCoverage.cutContained.encode :=
    .mp hcutGuard (.closed source_cut_contained)
  have hcases : Context Γ (either (member 41 3) (neg (member 41 3))) :=
    .closed (CompactHilbertBasis.identity (neg (member 41 3)))
  apply Context.disjunctionElim hcases
  · let Δ := member 41 3 :: Γ
    have hcut : Context Δ (member 41 3) := .head _ _
    have hguard : Context Δ seedFullGuard.encode := Context.conjunctionIntro
      (.under hspan (member 41 3)) (Context.conjunctionIntro (.under hseed (member 41 3))
        (Context.conjunctionIntro (.under hcontained (member 41 3))
          (Context.conjunctionIntro (.under hm (member 41 3)) hcut)))
    exact .mp hguard (.closed full_seed_coverage)
  · let Δ := neg (member 41 3) :: Γ
    have hn : Context Δ (neg (member 41 3)) := .head _ _
    have htargetFilter' : Context Δ targetFilter.encode := .under htargetFilter (neg (member 41 3))
    have hm' : Context Δ (member 8 3) := .under hm (neg (member 41 3))
    have hsuffix : Context Δ (member 38 3) := .mp hn (.mp hm' (.mp htargetFilter' (.closed target_point_in_suffix)))
    have hguard : Context Δ PASoundness.PAtoCompactSeededSpanSuffixReverseCoverage.guard.encode :=
      Context.conjunctionIntro (.under hfirst (neg (member 41 3)))
        (Context.conjunctionIntro (.under hsecond (neg (member 41 3)))
          (Context.conjunctionIntro (.under hspan (neg (member 41 3)))
            (Context.conjunctionIntro (.under hsourceFilter (neg (member 41 3)))
              (Context.conjunctionIntro hm' hsuffix))))
    exact .mp hguard (.closed suffix_reverse_coverage)

/-- All whole-target points have an actual graph9 preimage in whole0 under
the same fixed guard. -/
def reverse_coverage : KDerivation (imp globalGuard.encode reverseCoverage.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [globalGuard.encode]
  have hg : Context Γ globalGuard.encode := .head _ _
  have hp : Context Γ point.encode := .mp hg (.closed reverse_coverage_point)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 3 h)) := by
    intro h hh
    have he : h = globalGuard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 3 globalGuard (by decide)
  have hall := Context.generalize 3 hv hp
  simpa only [reverseCoverage,Formula.encode] using hall

theorem reverse_coverage_certificate : theoremCode (certificate reverse_coverage) =
    imp globalGuard.encode reverseCoverage.encode := certificate_correct reverse_coverage

end PASoundness.PAtoCompactSeededSpanReverseCoverage

#print axioms PASoundness.PAtoCompactSeededSpanReverseCoverage.globalGuard
#print axioms PASoundness.PAtoCompactSeededSpanReverseCoverage.output
#print axioms PASoundness.PAtoCompactSeededSpanReverseCoverage.point
#print axioms PASoundness.PAtoCompactSeededSpanReverseCoverage.reverseCoverage
#print axioms PASoundness.PAtoCompactSeededSpanReverseCoverage.reverse_coverage_point
#print axioms PASoundness.PAtoCompactSeededSpanReverseCoverage.reverse_coverage
#print axioms PASoundness.PAtoCompactSeededSpanReverseCoverage.reverse_coverage_certificate
