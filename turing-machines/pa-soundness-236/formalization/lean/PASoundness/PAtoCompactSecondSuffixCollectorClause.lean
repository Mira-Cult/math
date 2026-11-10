import PASoundness.PAtoCompactFirstSuffixCollectorClause
import PASoundness.PAtoCompactFirstSpanTargetOutside
import PASoundness.PAtoCompactScopedActiveReplace

/-! Relocate the clean first-suffix collector clause to the supplied second
suffix graph and its own whole, cut and filter. -/
namespace PASoundness.PAtoCompactSecondSuffixCollectorClause

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactCommonSourceSpanImages
open PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage PASoundness.PAtoCompactFirstSpanPathOutside
open PASoundness.PAtoCompactFirstSpanTargetOutside

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def frame : Formula := .imp firstBijection (.imp outsideGuard firstClause)
private def moved38 : Formula := replace 31 38 frame
private def moved7 : Formula := replace 6 7 moved38
private def moved8 : Formula := replace 0 8 moved7

/-- The actual graph7 and its filter supply secondClause, including uniqueness
against all whole-target competitors. -/
def second_collector_clause : KDerivation (imp secondBijection.encode
    (imp targetGuard.encode secondClause.encode)) := by
  have hbase : KDerivation frame.encode := by
    simpa only [frame, Formula.encode] using PASoundness.PAtoCompactFirstSuffixCollectorClause.first_collector_clause
  have h38 := replace_derivation 31 38 frame (by decide) (by decide) hbase
  have h7 := replace_derivation 6 7 moved38 (by decide) (by decide) (by simpa only [moved38] using h38)
  have h8 := replace_derivation 0 8 moved7 (by decide) (by decide) (by simpa only [moved7] using h7)
  have h41 := replace_derivation 40 41 moved8 (by decide) (by decide) (by simpa only [moved8] using h8)
  have halign : replace 40 41 moved8 = .imp secondBijection (.imp targetGuard secondClause) := by decide
  rw [halign] at h41
  exact h41

theorem second_collector_clause_certificate : theoremCode (certificate second_collector_clause) =
    imp secondBijection.encode (imp targetGuard.encode secondClause.encode) := certificate_correct second_collector_clause

end PASoundness.PAtoCompactSecondSuffixCollectorClause

#print axioms PASoundness.PAtoCompactSecondSuffixCollectorClause.second_collector_clause
#print axioms PASoundness.PAtoCompactSecondSuffixCollectorClause.second_collector_clause_certificate
