import PASoundness.PAtoCompactSeededSpanTargetCutContained
import PASoundness.PAtoCompactSeededSpanSeedReverseCoverage
import PASoundness.PAtoCompactScopedActiveReplace

/-! The source-side cut containment follows by capture-safe K relocation of
the target-side proof, retaining the source candidate and actual cut relation. -/
namespace PASoundness.PAtoCompactSeededSpanSourceCutContained

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactScopedActiveReplace

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guard : Formula := namedBoth (namedCandidate 0) (namedEither (.equal 40 0) (.member 0 40))
private def original : Formula := .imp PASoundness.PAtoCompactSeededSpanTargetCutContained.guard
  PASoundness.PAtoCompactSeededSpanSeedForwardCoverage.cutContained
private def at0 : Formula := replace 8 0 original

/-- The source whole's candidate condition and actual cut relation yield
the literal inclusion cut40⊆whole0. -/
def source_cut_contained : KDerivation (imp guard.encode
    PASoundness.PAtoCompactSeededSpanSeedReverseCoverage.cutContained.encode) := by
  have hbase : KDerivation original.encode := by
    simpa only [original,Formula.encode] using PASoundness.PAtoCompactSeededSpanTargetCutContained.target_cut_contained
  have h0 := replace_derivation 8 0 original (by decide) (by decide) hbase
  have h40 := replace_derivation 41 40 at0 (by decide) (by decide) (by simpa only [at0] using h0)
  have ha : replace 41 40 at0 = .imp guard PASoundness.PAtoCompactSeededSpanSeedReverseCoverage.cutContained := by decide
  rw [ha] at h40
  exact h40

theorem source_cut_contained_certificate : theoremCode (certificate source_cut_contained) =
    imp guard.encode PASoundness.PAtoCompactSeededSpanSeedReverseCoverage.cutContained.encode :=
  certificate_correct source_cut_contained

end PASoundness.PAtoCompactSeededSpanSourceCutContained

#print axioms PASoundness.PAtoCompactSeededSpanSourceCutContained.guard
#print axioms PASoundness.PAtoCompactSeededSpanSourceCutContained.source_cut_contained
#print axioms PASoundness.PAtoCompactSeededSpanSourceCutContained.source_cut_contained_certificate
