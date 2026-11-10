import PASoundness.PAtoCompactGuardBaseTransport
import PASoundness.PAtoCompactCandidateBinderBridge
import PASoundness.PAtoCompactPartialCompositionAtSource

/-! Convert an allocated domain predicate to the exact named candidate code
used by the guarded addition functionality proof. -/
namespace PASoundness.PAtoCompactDomainToNamedCandidate

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactPartialCompositionAtSource PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactCandidateFieldTransport PASoundness.PAtoCompactCandidateBinderBridge

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private theorem named_candidate_code (x : Nat) : (namedCandidate x).encode =
    candidateCode x 37 32 33 34 30 35 13 36 := by rfl

/-- The actual domain predicate at any valid base entails the exact named
candidate. The displayed side conditions ensure all field renamings are
capture-safe; they hold for the four fixed operand/result labels used here. -/
def domain_to_named_candidate (d x : Nat) (hxd : x < d + 32) (hx : x < 30) (h13 : x ≠ 13) :
    KDerivation (imp (domainAt d x).encode (namedCandidate x).encode) := by
  have h1 := transitivity_field x 132 133 134 135 136 137 138 139 32 33 (by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals omega)
  have h2 := member_field x 132 32 33 135 136 137 138 139 37 (by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals omega)
  have h3 := subset_field x 37 32 33 135 136 137 138 139 34 (by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals omega) (by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals omega)
  have h4 := subset_test_field x 37 32 33 34 136 137 138 139 30 (by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals omega) (by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals omega)
  have h5 := nonempty_field x 37 32 33 34 30 137 138 139 35 (by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals omega)
  have h6 := witness_field x 37 32 33 34 30 35 138 139 13 (by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals omega) (by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals omega)
  have h7 := order_field x 37 32 33 34 30 35 13 139 36 (by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals omega) (by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals omega)
  have hbase : KDerivation (imp (domainAt 100 x).encode (namedCandidate x).encode) := by
    rw [domainAt_encode, named_candidate_code]
    exact compose h1 (compose h2 (compose h3 (compose h4 (compose h5 (compose h6 h7)))))
  exact compose (domainAt_transport d 100 x hxd (by omega)) hbase

theorem domain_to_named_candidate_certificate (d x : Nat) (hxd : x < d + 32) (hx : x < 30) (h13 : x ≠ 13) :
    theoremCode (certificate (domain_to_named_candidate d x hxd hx h13)) =
      imp (domainAt d x).encode (namedCandidate x).encode := certificate_correct _

end PASoundness.PAtoCompactDomainToNamedCandidate

#print axioms PASoundness.PAtoCompactDomainToNamedCandidate.domain_to_named_candidate
#print axioms PASoundness.PAtoCompactDomainToNamedCandidate.domain_to_named_candidate_certificate
