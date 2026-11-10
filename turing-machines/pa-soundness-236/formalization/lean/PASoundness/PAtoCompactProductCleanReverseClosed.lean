import PASoundness.PAtoCompactProductCleanReverseConditional
import PASoundness.PAtoCompactProductFilterReverseTriple

/-! The supplied exact product filter preserves the literal reverse product
clause. The proof constructs the reflection premise from the same filter;
no product matrix, graph existence, row collection, or multiplication
soundness is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductCleanReverseClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductCleanFilter
open PASoundness.PAtoCompactProductCleanReverseConditional

/-- Under the exact filter, the existing reverse clause for graph 6 yields the
same clause for graph 54. No separate proof of triple reflection is needed. -/
def reverse_clause : KDerivation (imp (filterCode 54)
    (imp reverseFormula.encode (replace 6 54 reverseFormula).encode)) := by
  have hr := PASoundness.PAtoCompactProductFilterReverseTriple.reverse_triple 7 8 5
  have hp : KDerivation (imp (filterCode 54)
      (imp (triple 54 7 8 5).encode (triple 6 7 8 5).encode)) := by
    exact hr
  have h := reverse_clause_of_reflection hp
  change KDerivation (imp (filterCode 54) (imp (reverseAt 6).encode (reverseAt 54).encode)) at h
  simpa only [reverse_old, reverse_new] using h

theorem reverse_clause_certificate : theoremCode (certificate reverse_clause) =
    imp (filterCode 54) (imp reverseFormula.encode (replace 6 54 reverseFormula).encode) :=
  certificate_correct reverse_clause
end PASoundness.PAtoCompactProductCleanReverseClosed
#print axioms PASoundness.PAtoCompactProductCleanReverseClosed.reverse_clause
#print axioms PASoundness.PAtoCompactProductCleanReverseClosed.reverse_clause_certificate
