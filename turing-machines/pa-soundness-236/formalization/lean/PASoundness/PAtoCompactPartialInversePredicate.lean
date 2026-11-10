import PASoundness.PAtoCompactPartialInverseBase

/-! Capture-safe named predicate for applying candidate induction to a
partial inverse graph. The prefix induction variable is renamed from 8 to
30 so that 8 can be the later object-instance name while 30 is an internal
candidate test binder. This proves no successor step or global induction.
Named bottom still encodes literal compact code 1. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInversePredicate
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPartialInverseBase

/-- The original inverse-graph existence predicate, with prefix name 8. -/
def original : Formula := .ex 7 partialInverse

/-- The induction-variable name 30 is fresh in the original named formula. -/
theorem thirty_fresh : 30 ∉ original.names := by decide

/-- The predicate at a formally distinct induction-variable name. -/
def predicate : Formula := replace 8 30 original

/-- Names and binders are stated in the named proof IR; in particular the
three graph/domain parameters remain free. -/
theorem predicate_names : predicate.names = {0,1,2,3,6,7,19,20,21,22,30} := by decide
theorem predicate_binders : predicate.binders = {2,3,7,19,20,21,22} := by decide
theorem predicate_free : predicate.free = {0,1,6,30} := by decide
theorem induction_name_unbound : 30 ∉ predicate.binders := by decide
theorem instance_name_unbound : 8 ∉ predicate.binders := by decide

/-- Instantiating the renamed predicate at the original prefix name recovers
the exact original syntax; no semantic equivalence is substituted for it. -/
theorem instance_roundtrip : replace 30 8 predicate = original :=
  replace_roundtrip 8 30 original thirty_fresh

/-- The previously constructed K empty-prefix base is the literal instance
at 8 of the capture-safe predicate. -/
def empty_instance : KDerivation (imp (zeroCode 8 9) (replace 30 8 predicate).encode) := by
  rw [instance_roundtrip]
  exact empty_prefix_partial_inverse_exists

theorem empty_instance_certificate :
    theoremCode (certificate empty_instance) =
      imp (zeroCode 8 9) (replace 30 8 predicate).encode :=
  certificate_correct empty_instance

end PASoundness.PAtoCompactPartialInversePredicate

#print axioms PASoundness.PAtoCompactPartialInversePredicate.empty_instance
#print axioms PASoundness.PAtoCompactPartialInversePredicate.empty_instance_certificate
