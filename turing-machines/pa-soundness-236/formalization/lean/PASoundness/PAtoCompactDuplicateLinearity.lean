import PASoundness.PAtoCompactDuplicateDomain

/-! Raw global comparability fails even inside the proposed transitive and
extrema candidate domain, in the duplicate K model. This does not refute a
quotient-based order. -/
namespace PASoundness.PAtoCompactDuplicateLinearity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactMatrix
open PASoundness.CompactDuplicateModel PASoundness.PAtoCompactDuplicateDomain
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactGreatestSuccessor

private theorem mem10 (v : Nat) : mem 10 v = true ↔ v = 2 := by
  change bit 4 v = true ↔ v = 2
  rw [bit_eq_testBit]
  change (2 ^ 2).testBit v = true ↔ v = 2
  rw [Nat.testBit_two_pow]
  simp only [decide_eq_true_eq]
  exact eq_comm

private theorem mem18 (v : Nat) : mem 18 v = true ↔ v = 3 := by
  change bit 8 v = true ↔ v = 3
  rw [bit_eq_testBit]
  change (2 ^ 3).testBit v = true ↔ v = 3
  rw [Nat.testBit_two_pow]
  simp only [decide_eq_true_eq]
  exact eq_comm

def comparisonAssignment (i : Nat) : Nat := if i = 1 then 10 else if i = 2 then 18 else 0

private theorem candidate10 :
    Realize comparisonAssignment (decode (candidate 1 3 4 5 6 7 8 9 10)) := by
  simp only [candidate, oneLevelTransitiveCode, membersTransitiveCode, transitiveCode,
    greatestSubsetsCode, leastSubsetsCode, subsetCode, nonemptyCode, hasGreatestCode,
    greatestCode, leastMemberCode, CompactDerivations.either,
    CompactDuplicateModel.realize_both, CompactDuplicateModel.realize_all,
    CompactDuplicateModel.realize_imp, CompactDuplicateModel.realize_exists,
    CompactDuplicateModel.realize_neg, CompactDuplicateModel.realize_member,
    CompactDuplicateModel.realize_equal]
  simp [CompactMatrix.update, comparisonAssignment, mem10, empty_two]
  refine ⟨?_, ?_, ?_⟩
  · intro x v hx hv
    subst x
    rw [empty_two] at hv
    contradiction
  · intro u hu i hi
    refine ⟨i, hi, ?_⟩
    intro j hj hne
    exact (hne ((hu j hj).trans (hu i hi).symm)).elim
  · intro u hu i hi
    refine ⟨i, hi, ?_⟩
    intro j hj hne
    exact (hne ((hu j hj).trans (hu i hi).symm)).elim

private theorem candidate18 :
    Realize comparisonAssignment (decode (candidate 2 3 4 5 6 7 8 9 10)) := by
  simp only [candidate, oneLevelTransitiveCode, membersTransitiveCode, transitiveCode,
    greatestSubsetsCode, leastSubsetsCode, subsetCode, nonemptyCode, hasGreatestCode,
    greatestCode, leastMemberCode, CompactDerivations.either,
    CompactDuplicateModel.realize_both, CompactDuplicateModel.realize_all,
    CompactDuplicateModel.realize_imp, CompactDuplicateModel.realize_exists,
    CompactDuplicateModel.realize_neg, CompactDuplicateModel.realize_member,
    CompactDuplicateModel.realize_equal]
  simp [CompactMatrix.update, comparisonAssignment, mem18, empty_three]
  refine ⟨?_, ?_, ?_⟩
  · intro x v hx hv
    subst x
    rw [empty_three] at hv
    contradiction
  · intro u hu i hi
    refine ⟨i, hi, ?_⟩
    intro j hj hne
    exact (hne ((hu j hj).trans (hu i hi).symm)).elim
  · intro u hu i hi
    refine ⟨i, hi, ?_⟩
    intro j hj hne
    exact (hne ((hu j hj).trans (hu i hi).symm)).elim

/-- Global raw comparability of candidate elements, with distinct names. -/
def rawComparability : Nat :=
  imp (candidate 1 3 4 5 6 7 8 9 10)
    (imp (candidate 2 3 4 5 6 7 8 9 10)
      (either (equal 1 2) (either (member 1 2) (member 2 1))))

theorem raw_comparability_fails : ¬ Realize comparisonAssignment (decode rawComparability) := by
  simp only [rawComparability, realize_imp, CompactDerivations.either, realize_neg,
    realize_equal, realize_member]
  intro h
  have he := h candidate10 candidate18
  simp [comparisonAssignment, CompactDuplicateModel.mem, CompactMatrix.bit] at he

/-- K cannot prove raw global comparability for this candidate. -/
theorem raw_comparability_not_provable : ¬ KProves rawComparability := by
  rintro ⟨d⟩
  exact raw_comparability_fails (derivation_sound d comparisonAssignment)

end PASoundness.PAtoCompactDuplicateLinearity

#print axioms PASoundness.PAtoCompactDuplicateLinearity.raw_comparability_not_provable
