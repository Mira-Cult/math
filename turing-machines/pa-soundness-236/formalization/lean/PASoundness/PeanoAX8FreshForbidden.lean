import PASoundness.PeanoAX8DecodedFresh

/-! Finite-name avoidance for a decoded AX8 predicate. -/
namespace PASoundness.PeanoAX8FreshForbidden
open Peano CompactLogicalTransport

/-- A fresh index can avoid every free variable of the decoded predicate and
every additional finitely many forbidden names, without distinctness
assumptions on those names. -/
theorem exists_fresh_avoiding (c : Nat) (forbidden : Finset Nat) :
    ∃ j, j ∉ (interpreted c).freeVarFinset ∧ j ∉ forbidden := by
  let support := (interpreted c).freeVarFinset ∪ forbidden
  let j := support.sup id + 1
  have hj : j ∉ support := by
    intro h
    have hle : j ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [j] at hle
    omega
  exact ⟨j, by intro h; exact hj (Finset.mem_union_left _ h),
    by intro h; exact hj (Finset.mem_union_right _ h)⟩

end PASoundness.PeanoAX8FreshForbidden

#print axioms PASoundness.PeanoAX8FreshForbidden.exists_fresh_avoiding
