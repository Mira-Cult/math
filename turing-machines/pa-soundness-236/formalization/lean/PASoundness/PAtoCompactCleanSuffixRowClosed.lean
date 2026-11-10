import PASoundness.PAtoCompactCleanSuffixRowPackage
import PASoundness.PAtoCompactFixedFirstRowSuffixTarget40

/-! The same clean suffix isomorphism graph can be chosen before constructing
the full-prefix fixed-first row graph. This retains the actual clean F graph
inside the same K existential scope. It does not establish multiplication,
product-matrix clauses, or a PA interpretation. -/
namespace PASoundness.PAtoCompactCleanSuffixRowClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactCleanSuffixRowPackage
open PASoundness.PAtoCompactFixedFirstRowSuffixTarget40

/-- From the candidate index and the literal suffix equivalence, K constructs
one clean suffix graph and, using that graph, a full-prefix weak row graph. -/
def clean_suffix_with_row : KDerivation
    (imp candidate (imp (equivAt 31 40).encode result.encode)) := by
  apply package_of_row
  simpa [candidate,suffixBijection,rowResult,mapBijection40] using row_exists_at_40

theorem clean_suffix_with_row_certificate :
    theoremCode (certificate clean_suffix_with_row) =
      imp candidate (imp (equivAt 31 40).encode result.encode) := certificate_correct _
end PASoundness.PAtoCompactCleanSuffixRowClosed
#print axioms PASoundness.PAtoCompactCleanSuffixRowClosed.clean_suffix_with_row
#print axioms PASoundness.PAtoCompactCleanSuffixRowClosed.clean_suffix_with_row_certificate
