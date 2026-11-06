import Shared.Beeping.NPcoNP.NativeHalfCleanupComposed

/-! Protected-prefix facts for the tape produced by the exceptional HALF
cleanup.  These are useful for a separately proved return scan.  The base
tape is arbitrary, so this file does not assert that a delimiter exists or
that state 23 progresses. -/

namespace Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix

open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.UnarySuffixShift

/-- Exact tape at the state-23 boundary of `exceptional_through_cleanup`. -/
def postTape (base : Int → Bool) (b : Int) (values : List Nat) : Int → Bool :=
  let suffix := false :: UnaryBank.encode values
  let p := b + 3 + (suffix.length : Int)
  spec (after base (b+1) suffix) p ((UnaryBank.encode values).length + 2)

/-- The cleanup never alters the protected prefix up through its old head. -/
theorem postTape_prefix (base : Int → Bool) (b i : Int) (values : List Nat)
    (hi : i ≤ b) : postTape base b values i = base i := by
  unfold postTape
  have hout : i < b + 3 + (((false :: UnaryBank.encode values).length : Nat) : Int) -
      (((UnaryBank.encode values).length + 2 : Nat) : Int) := by
    simp only [List.length_cons, Nat.cast_succ, Nat.cast_add, Nat.cast_ofNat]
    omega
  rw [spec_outside _ _ _ _ (Or.inl hout)]
  exact after_prefix base (b+1) i (false :: UnaryBank.encode values) (by omega)

/-- A finite downward bit pattern on the protected prefix remains present
after cleanup, including any supplied delimiter. -/
theorem downHolds_postTape (base : Int → Bool) (b h : Int) (values : List Nat)
    (xs : List Bool) (hh : h ≤ b) (hm : downHolds base h xs) :
    downHolds (postTape base b values) h xs := by
  induction xs generalizing h with
  | nil => trivial
  | cons x xs ih =>
    simp only [downHolds] at hm ⊢
    constructor
    · rw [postTape_prefix base b h values hh]
      exact hm.1
    · exact ih (h-1) (by omega) hm.2

end Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
