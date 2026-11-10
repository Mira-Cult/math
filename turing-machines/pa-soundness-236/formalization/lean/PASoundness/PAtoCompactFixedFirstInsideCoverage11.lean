import PASoundness.PAtoCompactFixedFirstInsideCoverage

/-! Capture-safe specialization of the conditional inside-coverage theorem
from row-graph name 12 to row-graph name 11. The top witness remains an
explicit antecedent. No graph existence or pair-representative uniqueness is
asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstInsideCoverage11
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactFixedFirstCoverageBase PASoundness.PAtoCompactFixedFirstInsideCoverage
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The fixed top witness at row graph name 11. -/
def topWitness11 : Formula := replace 12 11 topWitness
private def packaged : Formula := .imp (namedSuccessor 0 1 2)
  (.imp (coverage 12) (.imp topWitness (replace 0 1 (coverage 12))))
private theorem packaged_code : packaged.encode = imp (successorCode 0 1 2)
    (imp (coverage 12).encode (imp topWitness.encode (replace 0 1 (coverage 12)).encode)) := by rfl
private theorem renamed_shape : replace 12 11 packaged = .imp (namedSuccessor 0 1 2)
    (.imp (coverage 11) (.imp topWitness11 (replace 0 1 (coverage 11)))) := by decide

/-- Exact graph-name-11 version of the K coverage assembly. -/
def inside_coverage11 : KDerivation (imp (successorCode 0 1 2)
    (imp (coverage 11).encode (imp topWitness11.encode
      (replace 0 1 (coverage 11)).encode))) := by
  have hd : KDerivation packaged.encode := by simpa [packaged_code] using inside_coverage
  have hi := universalInstance 12 11 packaged (by decide) (by decide) (by decide)
  rw [renamed_shape] at hi
  have hc := KDerivation.mp (.generalize 12 hd) hi
  simpa [namedSuccessor,namedSuccessorBody,namedBoth,namedEither,Formula.encode,
    Formula.not,successorCode,both,neg,either] using hc

theorem inside_coverage11_certificate : theoremCode (certificate inside_coverage11) =
    imp (successorCode 0 1 2) (imp (coverage 11).encode (imp topWitness11.encode
      (replace 0 1 (coverage 11)).encode)) := certificate_correct inside_coverage11
end PASoundness.PAtoCompactFixedFirstInsideCoverage11
#print axioms PASoundness.PAtoCompactFixedFirstInsideCoverage11.inside_coverage11
#print axioms PASoundness.PAtoCompactFixedFirstInsideCoverage11.inside_coverage11_certificate
