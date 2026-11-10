import PASoundness.PAtoCompactMultiplicationReverseClauseFromCases

/-! Syntactic bridge for independently constructed witnesses with the same
literal rebased multiplication reverse-clause shape. -/
namespace PASoundness.PAtoCompactMultiplicationReverseWitnessShape
open PASoundness.CompactNamed PASoundness.PAtoCompactMultiplicationReverseClauseFromCases

/-- Any named witness exhibited as the body of the exact reverse clause is
identical to the extracted witness; this is purely syntax and assumes no
semantic equivalence. -/
theorem witness_of_shape (w : Formula)
    (h : rebasedReverse = .all 5 (.imp (.member 45 5) w)) :
    reverseWitness5 = w := by
  unfold reverseWitness5
  rw [h]

end PASoundness.PAtoCompactMultiplicationReverseWitnessShape
#print axioms PASoundness.PAtoCompactMultiplicationReverseWitnessShape.witness_of_shape
