import PASoundness.PAtoCompactMultiplicationNewNewCase
import PASoundness.PAtoCompactMultiplicationLexSharedContext

/-! Supply the concrete shared context's actual K projections to the
new/new case. The shared context and both row branches remain literal K
antecedents; no graph construction or multiplication totality is asserted. -/
namespace PASoundness.PAtoCompactMultiplicationNewNewCaseClosed
open PASoundness.CompactProof
open PASoundness.PAtoCompactMultiplicationFourCaseLex
open PASoundness.PAtoCompactMultiplicationNewNewCase
open PASoundness.PAtoCompactMultiplicationLexSharedContext

/-- The concrete shared context supplies the clean ordered suffix needed by
the two explicit new-row branches. -/
def new_new_case : KDerivation (imp sharedPremise.encode
    (imp newFirst (imp newSecond comparisons))) :=
  new_new_from_projections sharedPremise.encode suffix_order_projection suffix_clean_projection

theorem new_new_case_certificate : theoremCode (certificate new_new_case) =
    imp sharedPremise.encode (imp newFirst (imp newSecond comparisons)) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationNewNewCaseClosed
#print axioms PASoundness.PAtoCompactMultiplicationNewNewCaseClosed.new_new_case
#print axioms PASoundness.PAtoCompactMultiplicationNewNewCaseClosed.new_new_case_certificate
