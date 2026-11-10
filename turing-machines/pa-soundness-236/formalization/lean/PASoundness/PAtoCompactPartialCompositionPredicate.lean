import PASoundness.PAtoCompactPartialCompositionBase

/-! Capture-safe predicate for candidate induction on partial composition
prefixes. Source 0, middle 1, target 8, and input graphs 6 and 7 remain
parameters; output graph 9 is existentially bound. This does not establish a
successor step, global induction, or graph collection. Code 1 is literal
compact bottom. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionPredicate
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPartialCompositionBase

/-- Partial-composition graph existence with original prefix name 10. -/
def original : Formula := .ex 9 partialComposition

/-- Formal induction name 30 does not occur in the original formula. -/
theorem thirty_fresh : 30 ∉ original.names := by decide

/-- Candidate-induction predicate with prefix 10 replaced by the fresh name 30. -/
def predicate : Formula := replace 10 30 original

theorem predicate_names : predicate.names = {0,1,2,3,4,6,7,8,9,19,20,21,22,30} := by decide
theorem predicate_binders : predicate.binders = {2,3,4,9,19,20,21,22} := by decide
theorem predicate_free : predicate.free = {0,1,6,7,8,30} := by decide
theorem induction_name_unbound : 30 ∉ predicate.binders := by decide
theorem instance_name_unbound : 25 ∉ predicate.binders := by decide

/-- Returning the formal prefix name 30 to 10 recovers the literal syntax. -/
theorem instance_roundtrip : replace 30 10 predicate = original :=
  replace_roundtrip 10 30 original thirty_fresh

/-- Existing K empty-prefix construction, written in the new predicate's
literal instance at name 10. -/
def empty_instance : KDerivation (imp (zeroCode 10 11) (replace 30 10 predicate).encode) := by
  rw [instance_roundtrip]
  exact empty_prefix_partial_composition_exists

theorem empty_instance_certificate :
    theoremCode (certificate empty_instance) =
      imp (zeroCode 10 11) (replace 30 10 predicate).encode :=
  certificate_correct empty_instance

end PASoundness.PAtoCompactPartialCompositionPredicate

#print axioms PASoundness.PAtoCompactPartialCompositionPredicate.empty_instance
#print axioms PASoundness.PAtoCompactPartialCompositionPredicate.empty_instance_certificate
