import PASoundness.PAtoCompactPartialCompositionPredicate

/-! Exact capture-safe prefix instances of the partial-composition induction
predicate. These are named-syntax identities, not collection or induction
proofs. Compact bottom remains the literal encoded code 1. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionPredicateInstances
open PASoundness.CompactNamed
open PASoundness.PAtoCompactPartialCompositionBase
open PASoundness.PAtoCompactPartialCompositionPredicate

/-- The next-prefix instance retains one existential graph witness. -/
theorem successor_instance : replace 30 13 predicate =
    .ex 9 (replace 10 13 partialComposition) := by decide

/-- The arbitrary candidate instance uses a label fresh for target name 8. -/
theorem candidate_instance : replace 30 25 predicate =
    .ex 9 (replace 10 25 partialComposition) := by decide

/-- The full-source instance is a partial graph over the entire source. -/
theorem source_instance : replace 30 0 predicate =
    .ex 9 (replace 10 0 partialComposition) := by decide

end PASoundness.PAtoCompactPartialCompositionPredicateInstances

#print axioms PASoundness.PAtoCompactPartialCompositionPredicateInstances.successor_instance
#print axioms PASoundness.PAtoCompactPartialCompositionPredicateInstances.source_instance
