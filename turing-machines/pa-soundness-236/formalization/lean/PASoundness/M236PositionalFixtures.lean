import PASoundness.M236Positional

/-! Checks of the four-tag aliases, binding, and strict-H translation. -/
namespace PASoundness.M236PositionalFixtures

open PASoundness.M236Game PASoundness.M236Positional

/-- Literal code zero is truth and also denotes truth implies truth. -/
theorem zero_implication (env : List Nat) : Truth4 (imp4 0 0) env := by
  rw [imp4_truth]
  intro h
  exact h

/-- Equality and membership remain distinct logical operations. -/
theorem distinct_atomic_meanings (x : Nat) :
    Truth4 (equal4 0 0) [x] ∧ ¬ Truth4 (member4 0 0) [x] := by
  constructor
  · rw [equal4_truth]
  · exact bottom4_false [x]

/-- A universal binder ranges over every natural and shadows at the head. -/
theorem universal_translation (f : Nat) (env : List Nat) :
    Truth (toStrict4 (all4 f)) env ↔ ∀ x, Truth4 f (x :: env) :=
  (toStrict4_truth _ _).trans (all4_truth _ _)

/-- Reverse translation treats strict zero as an ordinary membership atom,
which may be true for a suitable surrounding environment. -/
theorem strict_zero_origin : Truth4 (strictTo4 0) [0, 1] := by
  apply (strictTo4_truth 0 [0, 1]).mpr
  rw [Truth]
  simp [tag, payload, atom, PASoundness.Cantor.unpair, PASoundness.Cantor.unpairAux]

end PASoundness.M236PositionalFixtures
