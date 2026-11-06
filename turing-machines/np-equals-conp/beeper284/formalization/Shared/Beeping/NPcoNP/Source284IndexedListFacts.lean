import Shared.ComplexityBridge.TM2IndexedMap

/-! Generic list facts for the certified indexed traversal. These lemmas
concern list values only; runtime is supplied separately by the indexed-map
TM2 construction. -/
namespace Shared.Beeping.NPcoNP.Source284IndexedListFacts

open Shared.ComplexityBridge.TM2IndexedMap

variable {α β : Type}

@[simp] theorem length_indexed (F : Nat × α → β) (start : Nat) (xs : List α) :
    (indexed F start xs).length = xs.length := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih => simp [indexed, ih]

/-- Each output is the worker applied to the input at the same position and
its initial offset plus that position. -/
theorem getElem_indexed (F : Nat × α → β) (start : Nat) (xs : List α)
    (j : Nat) (h : j < xs.length) :
    (indexed F start xs)[j]'(by simpa using h) = F (start + j, xs[j]) := by
  induction xs generalizing start j with
  | nil => simp at h
  | cons x xs ih =>
    cases j with
    | zero => simp [indexed]
    | succ j =>
      have hj : j < xs.length := by simpa using h
      simpa [indexed, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (start + 1) j hj

end Shared.Beeping.NPcoNP.Source284IndexedListFacts
