import PASoundness.PAtoCompactSecondAdditionCutAllocation
import PASoundness.PAtoCompactSecondSuffixOrderWiden
import PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage
import PASoundness.PAtoCompactScopedActiveReplace

/-! Construct the clean graph7 for the second addition suffix from its
actual source1-to-suffix38 equivalence. -/
namespace PASoundness.PAtoCompactSecondAdditionCleanSuffixWitness

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactSuffixCleanWitness PASoundness.PAtoCompactFirstSpanTargetOutside
open PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage PASoundness.PAtoCompactSecondAdditionCutAllocation

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def cleanMatrix : Formula := namedBoth (namedBoth secondBijection
  PASoundness.PAtoCompactSecondSuffixOrderWiden.suffixOrder) targetClean
def output : Formula := .ex 7 cleanMatrix

private def frame : Formula := .imp suffixEquivalence (.ex 6 PASoundness.PAtoCompactSuffixCleanWitness.cleanMatrix)
private def cleanBody6 : Formula := replace 31 38 PASoundness.PAtoCompactSuffixCleanWitness.cleanMatrix

/-- The new bound graph label is obtained by existential alpha conversion,
retaining one witness for the bijection, order and stored-pair cleanliness. -/
def second_clean_suffix_witness : KDerivation (imp suffixEquivalence38.encode output.encode) := by
  have hbase : KDerivation frame.encode := by
    simpa only [frame, Formula.encode] using suffix_clean_witness
  have h38 := replace_derivation 31 38 frame (by decide) (by decide) hbase
  have halign : replace 31 38 frame = .imp suffixEquivalence38 (.ex 6 cleanBody6) := by decide
  rw [halign] at h38
  have halpha := (existentialAlpha 6 7 cleanBody6 (by decide) (by decide) (by decide)).1
  have hbody : replace 6 7 cleanBody6 = cleanMatrix := by decide
  rw [hbody] at halpha
  simpa only [output, Formula.encode] using compose h38 halpha

theorem second_clean_suffix_witness_certificate : theoremCode (certificate second_clean_suffix_witness) =
    imp suffixEquivalence38.encode output.encode := certificate_correct second_clean_suffix_witness

end PASoundness.PAtoCompactSecondAdditionCleanSuffixWitness

#print axioms PASoundness.PAtoCompactSecondAdditionCleanSuffixWitness.cleanMatrix
#print axioms PASoundness.PAtoCompactSecondAdditionCleanSuffixWitness.output
#print axioms PASoundness.PAtoCompactSecondAdditionCleanSuffixWitness.second_clean_suffix_witness
#print axioms PASoundness.PAtoCompactSecondAdditionCleanSuffixWitness.second_clean_suffix_witness_certificate
