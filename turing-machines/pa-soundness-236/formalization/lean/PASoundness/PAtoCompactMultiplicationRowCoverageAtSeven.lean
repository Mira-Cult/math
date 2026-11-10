import PASoundness.PAtoCompactMultiplicationRowCoveragePreserve

/-! Capture-safe specialization of quantified row coverage preservation to old
graph label 7, matching the initial row invariant. The point and new graph
remain supplied by a literal adjunction; this does not construct row graphs. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationRowCoverageAtSeven
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactMultiplicationRowGraphPreserve
open PASoundness.PAtoCompactMultiplicationRowCoveragePreserve
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Adjoining point 13 to old graph 7 preserves its quantified row coverage
in new graph 12; all bound labels avoid capture. -/
def coverage_all_preserved_at_seven : KDerivation
    (imp (namedAdjoin 7 13 12 14).encode
      (imp (coverageAll 7).encode (coverageAll 12).encode)) := by
  let f : Formula := .imp extension (.imp (coverageAll 11) (coverageAll 12))
  have hi := universalInstance 11 7 f (by decide) (by decide) (by decide)
  have hc : KDerivation f.encode := coverage_all_preserved
  have h := KDerivation.mp (.generalize 11 hc) hi
  have he : replace 11 7 f = .imp (namedAdjoin 7 13 12 14)
      (.imp (coverageAll 7) (coverageAll 12)) := by decide
  rw [he] at h
  exact h

theorem coverage_all_preserved_at_seven_certificate :
    theoremCode (certificate coverage_all_preserved_at_seven) =
      imp (namedAdjoin 7 13 12 14).encode
        (imp (coverageAll 7).encode (coverageAll 12).encode) :=
  certificate_correct coverage_all_preserved_at_seven
end PASoundness.PAtoCompactMultiplicationRowCoverageAtSeven
#print axioms PASoundness.PAtoCompactMultiplicationRowCoverageAtSeven.coverage_all_preserved_at_seven
#print axioms PASoundness.PAtoCompactMultiplicationRowCoverageAtSeven.coverage_all_preserved_at_seven_certificate
