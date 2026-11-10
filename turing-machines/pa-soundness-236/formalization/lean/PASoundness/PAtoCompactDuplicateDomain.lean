import PASoundness.CompactDuplicateModel
import PASoundness.PAtoCompactTransitiveDomain
import PASoundness.PAtoCompactLeastCounterexample

/-! The proposed one-level/extrema domain does not make its empty
representative unique in the nonextensional duplicate K model. This is a
semantic obstruction to raw equality, not a refutation of a quotient or a
different arithmetic interpretation. -/
namespace PASoundness.PAtoCompactDuplicateDomain
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactMatrix
open PASoundness.CompactDuplicateModel
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactGreatestSuccessor

def candidate (x b p q u k a m r : Nat) : Nat :=
  both (oneLevelTransitiveCode x b p q)
    (both (greatestSubsetsCode x u k m r) (leastSubsetsCode x u k a m r))

/-- The two distinct empty representatives each satisfy the candidate domain
fragment and the zero graph in a model of all K schemes. -/
theorem duplicate_zero_candidates :
    Realize (fun _ => 2) (decode (candidate 0 1 2 3 4 5 6 7 8)) ∧
    Realize (fun _ => 3) (decode (candidate 0 1 2 3 4 5 6 7 8)) ∧
    Realize (fun _ => 2) (decode (zeroCode 0 1)) ∧
    Realize (fun _ => 3) (decode (zeroCode 0 1)) ∧ (2 : Nat) ≠ 3 := by
  simp only [candidate, oneLevelTransitiveCode, membersTransitiveCode, transitiveCode,
    greatestSubsetsCode, leastSubsetsCode, subsetCode, nonemptyCode, hasGreatestCode,
    greatestCode, leastMemberCode, zeroCode, CompactDerivations.either,
    CompactDuplicateModel.realize_both, CompactDuplicateModel.realize_all,
    CompactDuplicateModel.realize_imp, CompactDuplicateModel.realize_exists,
    CompactDuplicateModel.realize_neg, CompactDuplicateModel.realize_member,
    CompactDuplicateModel.realize_equal]
  simp [CompactMatrix.update, CompactDuplicateModel.mem, CompactMatrix.bit_eq_testBit]
  constructor <;> intro x hx i hi <;> have := hx i <;> simp_all

end PASoundness.PAtoCompactDuplicateDomain

#print axioms PASoundness.PAtoCompactDuplicateDomain.duplicate_zero_candidates
