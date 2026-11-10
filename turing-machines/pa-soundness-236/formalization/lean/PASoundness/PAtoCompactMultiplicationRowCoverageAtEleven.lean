import PASoundness.PAtoCompactMultiplicationRowCoverageAtSeven

/-! Capture-safe specialization of old-index row-coverage preservation to
new graph name 11, matching the represented row successor construction. New
point coverage and row graph existence remain separate. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationRowCoverageAtEleven
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactMultiplicationRowCoveragePreserve
open PASoundness.PAtoCompactMultiplicationRowCoverageAtSeven
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Under the given adjunction 7→11, every old guarded index retains its
represented row edge with the same witnesses. -/
def coverage_all_preserved_at_eleven : KDerivation
    (imp (namedAdjoin 7 13 11 14).encode
      (imp (coverageAll 7).encode (coverageAll 11).encode)) := by
  let f : Formula := .imp (namedAdjoin 7 13 12 14)
    (.imp (coverageAll 7) (coverageAll 12))
  have hc : KDerivation f.encode := coverage_all_preserved_at_seven
  have hi := universalInstance 12 11 f (by decide) (by decide) (by decide)
  have h := KDerivation.mp (.generalize 12 hc) hi
  have he : replace 12 11 f = .imp (namedAdjoin 7 13 11 14)
      (.imp (coverageAll 7) (coverageAll 11)) := by decide
  rw [he] at h
  exact h

theorem coverage_all_preserved_at_eleven_certificate :
    theoremCode (certificate coverage_all_preserved_at_eleven) =
      imp (namedAdjoin 7 13 11 14).encode
        (imp (coverageAll 7).encode (coverageAll 11).encode) :=
  certificate_correct coverage_all_preserved_at_eleven
end PASoundness.PAtoCompactMultiplicationRowCoverageAtEleven
#print axioms PASoundness.PAtoCompactMultiplicationRowCoverageAtEleven.coverage_all_preserved_at_eleven
#print axioms PASoundness.PAtoCompactMultiplicationRowCoverageAtEleven.coverage_all_preserved_at_eleven_certificate
