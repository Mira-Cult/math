import PASoundness.PAtoCompactCandidateBinderBridge
import PASoundness.PAtoCompactQuotientSuccessor

/-! Capture-safe K binder alignment between the literal quotient-successor
candidate and the symmetry/transitivity candidate used by raw cancellation.
No quotient-successor witness or end-to-end PA result is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotSuccCandidateAlign
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateFieldTransport
open PASoundness.PAtoCompactCandidateBinderBridge PASoundness.PAtoCompactQuotientSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Rename each candidate binder through explicitly fresh names, for either
raw-successor witness name 0 or 1. These are literal K proof-data operations. -/
def candidate_align (x : Nat) (hx : x < 2) : KDerivation
    (imp (candidateCode x 30 31 32 33 34 35 36 37)
      (candidateCode x 37 32 33 34 30 35 10 36)) := by
  have h1 := member_field x 30 31 32 33 34 35 36 37 50 (by simp [List.nodup_cons]; omega)
  have h2 := transitivity_field x 50 31 32 33 34 35 36 37 51 52 (by simp [List.nodup_cons]; omega)
  have h3 := transitivity_field x 50 51 52 33 34 35 36 37 32 33 (by simp [List.nodup_cons]; omega)
  have h4 := subset_field x 50 32 33 33 34 35 36 37 53
    (by simp [List.nodup_cons]; omega) (by simp [List.nodup_cons]; omega)
  have h5 := subset_test_field x 50 32 33 53 34 35 36 37 30
    (by simp [List.nodup_cons]; omega) (by simp [List.nodup_cons]; omega)
  have h6 := witness_field x 50 32 33 53 30 35 36 37 10
    (by simp [List.nodup_cons]; omega) (by simp [List.nodup_cons]; omega)
  have h7 := order_field x 50 32 33 53 30 35 10 37 36
    (by simp [List.nodup_cons]; omega) (by simp [List.nodup_cons]; omega)
  have h8 := subset_field x 50 32 33 53 30 35 10 36 34
    (by simp [List.nodup_cons]; omega) (by simp [List.nodup_cons]; omega)
  have h9 := member_field x 50 32 33 34 30 35 10 36 37 (by simp [List.nodup_cons]; omega)
  exact compose h1 (compose h2 (compose h3 (compose h4 (compose h5 (compose h6 (compose h7 (compose h8 h9)))))))

/-- The actual named quotient-successor domain formula implies the exact
symmetry/transitivity candidate at the same displayed witness name. -/
def domain_to_symmetry (x : Nat) (hx : x < 2) : KDerivation
    (imp (domainFormula x).encode (candidateCode x 37 32 33 34 30 35 10 36)) := by
  simpa only [domainFormula, CompactNamed.encode_of_code] using candidate_align x hx

theorem domain_to_symmetry_certificate (x : Nat) (hx : x < 2) :
    theoremCode (certificate (domain_to_symmetry x hx)) =
      imp (domainFormula x).encode (candidateCode x 37 32 33 34 30 35 10 36) :=
  certificate_correct (domain_to_symmetry x hx)

end PASoundness.PAtoCompactQuotSuccCandidateAlign

#print axioms PASoundness.PAtoCompactQuotSuccCandidateAlign.domain_to_symmetry
#print axioms PASoundness.PAtoCompactQuotSuccCandidateAlign.domain_to_symmetry_certificate
