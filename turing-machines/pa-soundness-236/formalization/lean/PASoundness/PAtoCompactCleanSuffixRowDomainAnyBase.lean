import PASoundness.PAtoCompactCleanSuffixRow64
import PASoundness.PAtoCompactDomainCandidateReverse

/-! Supply the exact candidate guard for the same clean suffix and row graphs
from an allocated domain guard. This packages existing witnesses; no product
matrix or multiplication totality is claimed. -/
namespace PASoundness.PAtoCompactCleanSuffixRowDomainAnyBase
set_option maxRecDepth 65536
set_option maxHeartbeats 0
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactDomainCandidateReverse
open PASoundness.PAtoCompactCleanSuffixRow64

/-- At any allocation base, the source domain guard and the actual suffix
 equivalence construct one clean suffix graph and its same full row graph. -/
def clean_suffix_with_row_domain (base : Nat) : KDerivation
    (imp (domainAt base 31).encode (imp (PAtoCompactOrdinalAddition.equivAt 31 40).encode result64.encode)) := by
  have hd := domain_to_candidate 31 213 209 210 202 0 203 205 206 base (by decide) (by omega)
  exact compose hd clean_suffix_with_row64

theorem clean_suffix_with_row_domain_certificate (base : Nat) :
    theoremCode (certificate (clean_suffix_with_row_domain base)) =
      imp (domainAt base 31).encode (imp (PAtoCompactOrdinalAddition.equivAt 31 40).encode result64.encode) :=
  certificate_correct _
end PASoundness.PAtoCompactCleanSuffixRowDomainAnyBase
#print axioms PASoundness.PAtoCompactCleanSuffixRowDomainAnyBase.clean_suffix_with_row_domain
#print axioms PASoundness.PAtoCompactCleanSuffixRowDomainAnyBase.clean_suffix_with_row_domain_certificate
