import PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage
import PASoundness.PAtoCompactSeededSpanSeedForwardCoverage
import PASoundness.PAtoCompactSeededSpanTargetCutContained
import PASoundness.PAtoCompactSourceSuffixMembership

/-! Forward coverage of graph9 under a fixed explicit guard. A whole-source
point is split on cut membership; the seed or source-suffix construction
produces an actual output edge into whole8. This establishes coverage only,
not uniqueness, reverse coverage or a full graph bijection. -/
namespace PASoundness.PAtoCompactSeededSpanForwardCoverage

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactSeededSpanSeedSourceUnique PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage
open PASoundness.PAtoCompactSeededSpanTargetCutContained PASoundness.PAtoCompactSourceSuffixMembership
open PASoundness.PAtoCompactFirstSpanPathOutside PASoundness.PAtoCompactFirstSpanTargetOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def globalGuard : Formula := namedBoth fullSpan (namedBoth seedBijection (namedBoth (namedCandidate 8)
  (namedBoth (namedEither (.equal 41 8) (.member 8 41)) (namedBoth firstBijection
    (namedBoth secondBijection (namedBoth suffixFilter targetFilter))))))
def output : Formula := PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage.output
def point : Formula := .imp (.member 0 2) output
def forwardCoverage : Formula := .all 2 point

private def seedFrame : Formula := .imp PASoundness.PAtoCompactSeededSpanSeedForwardCoverage.guard
  PASoundness.PAtoCompactSeededSpanSeedForwardCoverage.output
private def seedFullGuard : Formula := namedBoth fullSpan (namedBoth seedBijection
  (namedBoth PASoundness.PAtoCompactSeededSpanSeedForwardCoverage.cutContained
    (namedBoth (.member 0 2) (.member 40 2))))
private theorem seed_frame_alignment : replace 10 1 seedFrame = .imp seedFullGuard output := by decide

private def full_seed_coverage : KDerivation (imp seedFullGuard.encode output.encode) := by
  have hbase : KDerivation seedFrame.encode := by
    simpa only [seedFrame,Formula.encode] using PASoundness.PAtoCompactSeededSpanSeedForwardCoverage.seed_forward_coverage
  have h := replace_derivation 10 1 seedFrame (by decide) (by decide) hbase
  rw [seed_frame_alignment] at h
  exact h

/-- For a whole-source point, either its seed edge or its suffix path yields
an actual graph9 edge into whole8 under the stated fixed global premises. -/
def forward_coverage_point : KDerivation (imp globalGuard.encode point.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 0 2,globalGuard.encode]
  have hm : Context Γ (member 0 2) := .head _ _
  have hg : Context Γ globalGuard.encode := .hypothesis (by simp [Γ])
  have hspan : Context Γ fullSpan.encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hseed : Context Γ seedBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hcandidate : Context Γ (namedCandidate 8).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hrel : Context Γ (either (equal 41 8) (member 8 41)) := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hfirst : Context Γ firstBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hsecond : Context Γ secondBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hsourceFilter : Context Γ suffixFilter.encode := Context.conjunctionLeft hr
  have htargetFilter : Context Γ targetFilter.encode := Context.conjunctionRight hr
  have hcutGuard : Context Γ PASoundness.PAtoCompactSeededSpanTargetCutContained.guard.encode :=
    Context.conjunctionIntro hcandidate hrel
  have hcontained : Context Γ PASoundness.PAtoCompactSeededSpanSeedForwardCoverage.cutContained.encode :=
    .mp hcutGuard (.closed target_cut_contained)
  have hcases : Context Γ (either (member 40 2) (neg (member 40 2))) :=
    .closed (CompactHilbertBasis.identity (neg (member 40 2)))
  apply Context.disjunctionElim hcases
  · let Δ := member 40 2 :: Γ
    have hcut : Context Δ (member 40 2) := .head _ _
    have hguard : Context Δ seedFullGuard.encode := Context.conjunctionIntro
      (.under hspan (member 40 2)) (Context.conjunctionIntro (.under hseed (member 40 2))
        (Context.conjunctionIntro (.under hcontained (member 40 2))
          (Context.conjunctionIntro (.under hm (member 40 2)) hcut)))
    exact .mp hguard (.closed full_seed_coverage)
  · let Δ := neg (member 40 2) :: Γ
    have hn : Context Δ (neg (member 40 2)) := .head _ _
    have hsourceFilter' : Context Δ suffixFilter.encode := .under hsourceFilter (neg (member 40 2))
    have hm' : Context Δ (member 0 2) := .under hm (neg (member 40 2))
    have hsuffix : Context Δ (member 31 2) := .mp hn (.mp hm' (.mp hsourceFilter' (.closed source_point_in_suffix)))
    have hguard : Context Δ PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage.guard.encode :=
      Context.conjunctionIntro (.under hfirst (neg (member 40 2)))
        (Context.conjunctionIntro (.under hsecond (neg (member 40 2)))
          (Context.conjunctionIntro (.under hspan (neg (member 40 2)))
            (Context.conjunctionIntro (.under htargetFilter (neg (member 40 2)))
              (Context.conjunctionIntro hm' hsuffix))))
    exact .mp hguard (.closed suffix_forward_coverage)

/-- All whole-source points have an actual graph9 image in whole8 under the
same fixed guard. -/
def forward_coverage : KDerivation (imp globalGuard.encode forwardCoverage.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [globalGuard.encode]
  have hg : Context Γ globalGuard.encode := .head _ _
  have hp : Context Γ point.encode := .mp hg (.closed forward_coverage_point)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    have he : h = globalGuard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 2 globalGuard (by decide)
  have hall := Context.generalize 2 hv hp
  simpa only [forwardCoverage,Formula.encode] using hall

theorem forward_coverage_certificate : theoremCode (certificate forward_coverage) =
    imp globalGuard.encode forwardCoverage.encode := certificate_correct forward_coverage

end PASoundness.PAtoCompactSeededSpanForwardCoverage

#print axioms PASoundness.PAtoCompactSeededSpanForwardCoverage.globalGuard
#print axioms PASoundness.PAtoCompactSeededSpanForwardCoverage.output
#print axioms PASoundness.PAtoCompactSeededSpanForwardCoverage.point
#print axioms PASoundness.PAtoCompactSeededSpanForwardCoverage.forwardCoverage
#print axioms PASoundness.PAtoCompactSeededSpanForwardCoverage.forward_coverage_point
#print axioms PASoundness.PAtoCompactSeededSpanForwardCoverage.forward_coverage
#print axioms PASoundness.PAtoCompactSeededSpanForwardCoverage.forward_coverage_certificate
