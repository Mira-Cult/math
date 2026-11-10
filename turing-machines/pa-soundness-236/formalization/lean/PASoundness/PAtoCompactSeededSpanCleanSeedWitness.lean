import PASoundness.PAtoCompactSuffixCleanWitness
import PASoundness.PAtoCompactSeededSpanCleanEndpoints
import PASoundness.PAtoCompactSeededSpanSeedSourceUnique
import PASoundness.PAtoCompactSeededSpanOrderFreshening

/-! A supplied cut-to-cut equivalence provides an actual clean seed graph,
with its bijection and order on that same graph. -/
namespace PASoundness.PAtoCompactSeededSpanCleanSeedWitness

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactSuffixCleanWitness PASoundness.PAtoCompactSeededSpanSeedSourceUnique
open PASoundness.PAtoCompactSeededSpanOrderFreshening PASoundness.PAtoCompactSeededSpanCleanEndpoints

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def seedEquivalence : Formula := replace 31 41 (replace 1 40 suffixEquivalence)
def seedMatrix : Formula := namedBoth (namedBoth seedBijection seedOriginal) seedClean
def output : Formula := .ex 14 seedMatrix

private def frame : Formula := .imp suffixEquivalence (.ex 6 cleanMatrix)
private def moved40 : Formula := replace 1 40 frame
private def cleanBody6 : Formula := replace 31 41 (replace 1 40 cleanMatrix)

/-- The graph14 witness is alpha-renamed from the actual clean graph witness;
both the old and new graph-label freshness conditions are checked. -/
def clean_seed_witness : KDerivation (imp seedEquivalence.encode output.encode) := by
  have hbase : KDerivation frame.encode := by
    simpa only [frame, Formula.encode] using suffix_clean_witness
  have h40 := replace_derivation 1 40 frame (by decide) (by decide) hbase
  have h41 := replace_derivation 31 41 moved40 (by decide) (by decide) (by simpa only [moved40] using h40)
  have halign : replace 31 41 moved40 = .imp seedEquivalence (.ex 6 cleanBody6) := by decide
  rw [halign] at h41
  have halpha := (existentialAlpha 6 14 cleanBody6 (by decide) (by decide) (by decide)).1
  have hbody : replace 6 14 cleanBody6 = seedMatrix := by decide
  rw [hbody] at halpha
  simpa only [output, Formula.encode] using compose h41 halpha

theorem clean_seed_witness_certificate : theoremCode (certificate clean_seed_witness) =
    imp seedEquivalence.encode output.encode := certificate_correct clean_seed_witness

end PASoundness.PAtoCompactSeededSpanCleanSeedWitness

#print axioms PASoundness.PAtoCompactSeededSpanCleanSeedWitness.seedEquivalence
#print axioms PASoundness.PAtoCompactSeededSpanCleanSeedWitness.seedMatrix
#print axioms PASoundness.PAtoCompactSeededSpanCleanSeedWitness.output
#print axioms PASoundness.PAtoCompactSeededSpanCleanSeedWitness.clean_seed_witness
#print axioms PASoundness.PAtoCompactSeededSpanCleanSeedWitness.clean_seed_witness_certificate
