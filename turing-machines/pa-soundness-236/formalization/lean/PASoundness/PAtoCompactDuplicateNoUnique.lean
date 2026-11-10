import PASoundness.PAtoCompactDuplicateDomain

/-! A single-assignment K countermodel to raw uniqueness of zero inside the
specific transitivity/extrema candidate domain. This does not exclude a
quotient, a selected zero parameter, or another interpretation. -/
namespace PASoundness.PAtoCompactDuplicateNoUnique
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactMatrix
open PASoundness.CompactDuplicateModel PASoundness.PAtoCompactDuplicateDomain
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactGreatestSuccessor

def rawZeroUniqueness : Nat :=
  imp (candidate 1 3 4 5 6 7 8 9 10)
    (imp (zeroCode 1 3) (imp (candidate 2 3 4 5 6 7 8 9 10)
      (imp (zeroCode 2 3) (equal 1 2))))

theorem candidate_one_in_duplicate :
    Realize zeroAssignment (decode (candidate 1 3 4 5 6 7 8 9 10)) := by
  simp only [candidate, oneLevelTransitiveCode, membersTransitiveCode, transitiveCode,
    greatestSubsetsCode, leastSubsetsCode, subsetCode, nonemptyCode, hasGreatestCode,
    greatestCode, leastMemberCode, CompactDerivations.either,
    CompactDuplicateModel.realize_both, CompactDuplicateModel.realize_all,
    CompactDuplicateModel.realize_imp, CompactDuplicateModel.realize_exists,
    CompactDuplicateModel.realize_neg, CompactDuplicateModel.realize_member,
    CompactDuplicateModel.realize_equal]
  simp [CompactMatrix.update, zeroAssignment, CompactDuplicateModel.mem,
    CompactMatrix.bit_eq_testBit]
  constructor <;> intro x hx i hi <;> have := hx i <;> simp_all

theorem candidate_two_in_duplicate :
    Realize zeroAssignment (decode (candidate 2 3 4 5 6 7 8 9 10)) := by
  simp only [candidate, oneLevelTransitiveCode, membersTransitiveCode, transitiveCode,
    greatestSubsetsCode, leastSubsetsCode, subsetCode, nonemptyCode, hasGreatestCode,
    greatestCode, leastMemberCode, CompactDerivations.either,
    CompactDuplicateModel.realize_both, CompactDuplicateModel.realize_all,
    CompactDuplicateModel.realize_imp, CompactDuplicateModel.realize_exists,
    CompactDuplicateModel.realize_neg, CompactDuplicateModel.realize_member,
    CompactDuplicateModel.realize_equal]
  simp [CompactMatrix.update, zeroAssignment, CompactDuplicateModel.mem,
    CompactMatrix.bit_eq_testBit]
  constructor <;> intro x hx i hi <;> have := hx i <;> simp_all

/-- The exact raw-equality uniqueness implication is false in this K model. -/
theorem raw_zero_uniqueness_fails : ¬ Realize zeroAssignment (decode rawZeroUniqueness) := by
  rw [rawZeroUniqueness, realize_imp, realize_imp, realize_imp, realize_imp, realize_equal]
  intro h
  have h₁ : Realize zeroAssignment (decode (zeroCode 1 3)) := by
    apply (CompactDuplicateModel.zeroCode_realize 1 3 zeroAssignment (by decide)).mpr
    simpa [zeroAssignment] using empty_two
  have h₂ : Realize zeroAssignment (decode (zeroCode 2 3)) := by
    apply (CompactDuplicateModel.zeroCode_realize 2 3 zeroAssignment (by decide)).mpr
    simpa [zeroAssignment] using empty_three
  have he := h candidate_one_in_duplicate h₁ candidate_two_in_duplicate h₂
  simp [zeroAssignment] at he

/-- K cannot derive the displayed candidate-domain zero-uniqueness formula. -/
theorem raw_zero_uniqueness_not_provable : ¬ KProves rawZeroUniqueness := by
  rintro ⟨d⟩
  exact raw_zero_uniqueness_fails (derivation_sound d zeroAssignment)

end PASoundness.PAtoCompactDuplicateNoUnique

#print axioms PASoundness.PAtoCompactDuplicateNoUnique.raw_zero_uniqueness_not_provable
