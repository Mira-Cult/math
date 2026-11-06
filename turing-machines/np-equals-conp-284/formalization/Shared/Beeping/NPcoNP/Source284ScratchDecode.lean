import Shared.Beeping.NPcoNP.Source284ScratchTerminator

/-! Total executable decoding of the marked scratch stream. Each pair is
`payload,0`; `0,1` terminates. The recursion count is proved independent of
the arbitrary higher suffix. This is a mathematical decoder, not yet a
single-tape implementation or an elementary bit-cost simulation. -/
namespace Shared.Beeping.NPcoNP.Source284ScratchDecode

open Shared.Beeping.NPcoNP.Source284TableEncode (bit)
open Shared.Beeping.NPcoNP.Source284PayloadLoop (scratch)
open Shared.Beeping.NPcoNP.Source284ScratchTerminator (mark mark_low)

/-- Read two-bit blocks until the explicit terminator. Invalid blocks and a
zero stream are rejected; no classical decision oracle is used. -/
def decode (s : Nat) : Option (List Bool) :=
  if s%4 = 2 then some []
  else if s%4 < 2 ∧ 0 < s then
    (decode (s/4)).map (fun xs => decide (s%2 = 1)::xs)
  else none
termination_by s
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- Count recursive block inspections, including the terminator or a malformed
block. This is not an elementary bit-operation cost. -/
def inspections (s : Nat) : Nat :=
  if s%4 = 2 then 1
  else if s%4 < 2 ∧ 0 < s then 1+inspections (s/4)
  else 1
termination_by s
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem scratch_positive (w : List Bool) (suffix : Nat) : 0 < scratch w (mark suffix) := by
  induction w with
  | nil => simp [scratch,mark]
  | cons b bs ih => cases b <;> simp [scratch,bit] <;> omega

theorem decode_marked (w : List Bool) (suffix : Nat) :
    decode (scratch w (mark suffix)) = some w := by
  induction w with
  | nil => simp [scratch,decode,mark_low]
  | cons b bs ih =>
    have hp := scratch_positive bs suffix
    cases b <;> simp only [scratch,bit,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte]
    · rw [decode]
      simp [Nat.add_mod,Nat.mul_mod,ih,hp]
    · rw [decode]
      have hd : (1+4*scratch bs (mark suffix))/4 = scratch bs (mark suffix) := by omega
      simp [Nat.add_mod,Nat.mul_mod,hd,ih,hp]

theorem inspections_marked (w : List Bool) (suffix : Nat) :
    inspections (scratch w (mark suffix)) = w.length+1 := by
  induction w with
  | nil => simp [scratch,inspections,mark_low]
  | cons b bs ih =>
    have hp := scratch_positive bs suffix
    cases b <;> simp only [scratch,bit,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,List.length_cons]
    · rw [inspections]
      simp [Nat.add_mod,Nat.mul_mod,ih,hp] <;> omega
    · rw [inspections]
      have hd : (1+4*scratch bs (mark suffix))/4 = scratch bs (mark suffix) := by omega
      simp [Nat.add_mod,Nat.mul_mod,hd,ih,hp] <;> omega

/-- The terminator removes the ambiguity shown by `scratch_collision`:
different payloads cannot produce the same marked scratch stream, even when
their original ignored suffixes differ. -/
theorem marked_injective (w₁ w₂ : List Bool) (s₁ s₂ : Nat)
    (h : scratch w₁ (mark s₁) = scratch w₂ (mark s₂)) : w₁ = w₂ := by
  have hd := congrArg decode h
  rw [decode_marked,decode_marked] at hd
  exact Option.some.inj hd

example : decode 2 = some [] := by decide +kernel
example : decode 0 = none := by decide +kernel
example : decode (scratch [true,false,true] (mark 987)) = some [true,false,true] := by
  exact decode_marked _ _

end Shared.Beeping.NPcoNP.Source284ScratchDecode
