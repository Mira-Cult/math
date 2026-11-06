import Mathlib.Tactic

/-! Low-bit agreement for the natural-number tails used by the pinned 284
relative-direction evaluator. These are unbounded natural-number statements;
they do not assume a finite machine run or a complexity-theory result. -/

namespace Shared.Beeping.NPcoNP.Source284BitWindow

/-- The low `k` binary digits of two natural-number tails agree. -/
def Agree (k a b : Nat) : Prop := a % 2^k = b % 2^k

theorem agree_refl (k a : Nat) : Agree k a a := rfl

theorem agree_symm {k a b : Nat} (h : Agree k a b) : Agree k b a := h.symm

theorem agree_mono {j k a b : Nat} (hjk : j ≤ k) (h : Agree k a b) :
    Agree j a b := by
  exact Nat.ModEq.of_dvd (pow_dvd_pow 2 hjk) h

theorem agree_weaken {k a b : Nat} (h : Agree (k+1) a b) : Agree k a b :=
  agree_mono (by omega) h

/-- At positive depth the currently scanned low bits agree. -/
theorem agree_head {k a b : Nat} (h : Agree (k+1) a b) : a % 2 = b % 2 := by
  have h' := agree_mono (show 1 ≤ k+1 by omega) h
  simpa [Agree] using h'

/-- Popping the low bit reduces the known window by exactly one. -/
theorem agree_tail {k a b : Nat} (h : Agree (k+1) a b) : Agree k (a/2) (b/2) := by
  unfold Agree at *
  have h' := congrArg (fun n : Nat => n / 2) h
  simpa only [pow_succ, Nat.mul_comm (2^k) 2,
    Nat.mod_mul_right_div_self] using h'

/-- Prepending the same written digit preserves a low-bit agreement window.
The digit need not be binary; the evaluator later supplies 0 or 1. -/
theorem agree_push {k a b : Nat} (h : Agree k a b) (digit : Nat) :
    Agree k (2*a+digit) (2*b+digit) := by
  exact ((Nat.ModEq.refl 2).mul h).add (Nat.ModEq.refl digit)

/-- Discarding every bit at and above `k` preserves the first `k` bits. -/
theorem agree_truncate (k a : Nat) : Agree k a (a % 2^k) := by
  simp [Agree]

end Shared.Beeping.NPcoNP.Source284BitWindow
