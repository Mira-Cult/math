import PASoundness.PAtoCompactFixedFirstInsideCoverage11
import PASoundness.PAtoCompactFixedFirstTopCoverageEleven

/-! Syntactic alignment of the constructed top-coverage formula and the
antecedent of the quantified graph-11 coverage step. This proves no witness
existence or multiplication theorem. -/
namespace PASoundness.PAtoCompactFixedFirstTopCoverageAlignment
open PASoundness.CompactNamed
open PASoundness.PAtoCompactFixedFirstInsideCoverage11
open PASoundness.PAtoCompactFixedFirstTopCoverageEleven

/-- Both modules use the same existential F-edge and nested-pair witness. -/
theorem top_witness_alignment : topWitness11 = topCoverage11 := by decide
end PASoundness.PAtoCompactFixedFirstTopCoverageAlignment
#print axioms PASoundness.PAtoCompactFixedFirstTopCoverageAlignment.top_witness_alignment
