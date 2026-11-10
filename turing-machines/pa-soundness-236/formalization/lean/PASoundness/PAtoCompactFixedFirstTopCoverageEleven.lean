import PASoundness.PAtoCompactFixedFirstTopCoverage

/-! Capture-safe relocation of the fixed-first row top-coverage witness to
new graph label 11. This is one pointwise case with supplied witnesses, not a
row-collection or multiplication-totality theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstTopCoverageEleven
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactFixedFirstTopCoverage
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Coverage at source index 0 for F graph 6 and row graph 11. -/
def topCoverage11 : Formula := .ex 4 (.ex 5
  (namedBoth (graphFormula 6 0 4)
    (namedBoth (pairFormula 5 30 0) (graphFormula 11 5 4))))

private def original : Formula := .imp (graphFormula 6 0 4)
  (.imp (pairFormula 12 30 0) (.imp (pairFormula 13 12 4)
    (.imp (.member 7 13) topCoverage)))

private def relocated : Formula := .imp (graphFormula 6 0 4)
  (.imp (pairFormula 12 30 0) (.imp (pairFormula 13 12 4)
    (.imp (.member 11 13) topCoverage11)))

/-- The given F edge, coordinate pair, nested edge pair, and membership of
that nested pair in row graph 11 yield its concrete top-coverage witness. -/
def top_coverage11_from_witnesses : KDerivation
    (imp (graphFormula 6 0 4).encode
      (imp (pairFormula 12 30 0).encode
        (imp (pairFormula 13 12 4).encode
          (imp (member 11 13) topCoverage11.encode)))) := by
  have h : KDerivation original.encode := by
    simpa [original,Formula.encode] using top_coverage_from_witnesses
  have hi := universalInstance 7 11 original (by decide) (by decide) (by decide)
  have hr : replace 7 11 original = relocated := by decide
  rw [hr] at hi
  have hc := KDerivation.mp (.generalize 7 h) hi
  simpa [relocated,Formula.encode] using hc

theorem top_coverage11_from_witnesses_certificate :
    theoremCode (certificate top_coverage11_from_witnesses) =
      imp (graphFormula 6 0 4).encode
        (imp (pairFormula 12 30 0).encode
          (imp (pairFormula 13 12 4).encode
            (imp (member 11 13) topCoverage11.encode))) :=
  certificate_correct top_coverage11_from_witnesses
end PASoundness.PAtoCompactFixedFirstTopCoverageEleven
#print axioms PASoundness.PAtoCompactFixedFirstTopCoverageEleven.top_coverage11_from_witnesses
#print axioms PASoundness.PAtoCompactFixedFirstTopCoverageEleven.top_coverage11_from_witnesses_certificate
