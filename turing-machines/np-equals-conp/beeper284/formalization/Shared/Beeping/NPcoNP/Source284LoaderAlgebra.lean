import Shared.Beeping.NPcoNP.Source284Suffix

/-! Binary two-stack algebra for a fixed input loader.  The source's `left`
and `right` halves are low-bit-first naturals; a push writes one bit and a
transfer pops one bit from the right half and pushes it onto the left half.
This is arithmetic on a supplied list and certificate; no finite transition
table, blank-start reachability, or complexity bound is asserted here. -/

namespace Shared.Beeping.NPcoNP.Source284LoaderAlgebra

open Shared.Beeping.NPcoNP.Source284Parser (payloadFold payloadFold_value)
open Shared.Codes.BitNumeralCompare (value)

/-- A finite low-first bit prefix followed by an arbitrary higher tail. -/
def stack : List Bool → Nat → Nat
  | [], tail => tail
  | b :: bs, tail => 2 * stack bs tail + (if b then 1 else 0)

/-- Move exactly `count` low bits from the second half to the first. -/
def transfer : Nat → Nat → Nat → Nat × Nat
  | 0, left, right => (left, right)
  | count + 1, left, right =>
      transfer count (2 * left + right % 2) (right / 2)

theorem stack_value (bs : List Bool) (tail : Nat) :
    stack bs tail = 2 ^ bs.length * tail + value bs := by
  induction bs with
  | nil => simp [stack, value]
  | cons b bs ih =>
    simp only [stack, ih, List.length_cons, pow_succ, value]
    cases b <;> simp <;> ring

/-- Writing the input left-to-right pushes its reverse onto the current
half, above the unchanged certificate tail. -/
theorem pushed_eq_stack (bs : List Bool) (certificate : Nat) :
    payloadFold certificate bs = stack bs.reverse certificate := by
  rw [payloadFold_value, stack_value]
  simp

theorem stack_cons_mod (b : Bool) (bs : List Bool) (tail : Nat) :
    stack (b :: bs) tail % 2 = (if b then 1 else 0) := by
  cases b <;> simp [stack] <;> omega

theorem stack_cons_div (b : Bool) (bs : List Bool) (tail : Nat) :
    stack (b :: bs) tail / 2 = stack bs tail := by
  cases b <;> simp [stack] <;> omega

/-- Transferring a finite stack prefix returns its original higher tail and
pushes precisely the prefix bits onto the destination half. -/
theorem transfer_stack (bs : List Bool) (left tail : Nat) :
    transfer bs.length left (stack bs tail) = (payloadFold left bs, tail) := by
  induction bs generalizing left with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons, transfer, stack_cons_mod, stack_cons_div, payloadFold]
    exact ih _

/-- The complete forward/write and reverse/transfer data path preserves an
arbitrary certificate, including empty input and trailing-zero input bits. -/
theorem push_transfer (bs : List Bool) (certificate : Nat) :
    transfer bs.length 0 (payloadFold certificate bs) = (value bs, certificate) := by
  rw [pushed_eq_stack]
  simpa [payloadFold_value] using (transfer_stack bs.reverse 0 certificate)

end Shared.Beeping.NPcoNP.Source284LoaderAlgebra
