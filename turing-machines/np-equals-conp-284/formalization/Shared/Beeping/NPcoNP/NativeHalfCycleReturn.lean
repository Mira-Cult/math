import Shared.Beeping.NPcoNP.NativeHalfSuffixShift

/-! The transition after the literal native-HALF cycle's suffix shift. This
module proves a prepared local segment; it does not identify the branch with
the parity of the original operand or prove the complete HALF operation. -/
namespace Shared.Beeping.NPcoNP.NativeHalfCycleReturn

open Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.UnarySuffixShift

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem row31_zero : machine.table.row 31 false = ⟨false, .right, 18, false⟩ := by decide
theorem row31_one : machine.table.row 31 true = ⟨true, .right, 30, false⟩ := by decide

/-- The return reads the preceding cell without changing the tape or beeping. -/
theorem return_step (h : Int) (tape : Int → Bool) :
    machine.step (cfg 31 h tape) =
      (cfg (if tape h then 30 else 18) (h+1) tape, false) := by
  by_cases ht : tape h = true
  · have hw : (cfg 31 h tape : Config 284).write true = tape := by
      rw [← ht]
      exact write_current _
    change (⟨31,h,tape⟩ : Config 284).write true = tape at hw
    simp [cfg, Machine.step, ht, row31_one, Move.apply, hw]
  · have ht' : tape h = false := by cases hv : tape h <;> simp_all
    have hw : (cfg 31 h tape : Config 284).write false = tape := by
      rw [← ht']
      exact write_current _
    change (⟨31,h,tape⟩ : Config 284).write false = tape at hw
    simp [cfg, Machine.step, ht', row31_zero, Move.apply, hw]

/-- After the silent suffix shift, execute the return's one silent transition.
The branch is the protected tape bit left of the original gap. -/
theorem suffix_shift_and_return (base : Int → Bool) (gap : Int)
    (x : Nat) (xs : List Nat) :
    let suffix := UnaryBank.encode (x::xs)
    silentSegment machine
      (cfg 32 (gap+2) (before base gap suffix))
      (cfg (if base (gap-1) then 30 else 18) gap (after base gap suffix))
      (2*suffix.length + 4) := by
  dsimp only
  let suffix := UnaryBank.encode (x::xs)
  have hs := selected_suffix_shift base gap x xs
  have hv : after base gap suffix (gap-1) = base (gap-1) :=
    after_prefix base gap (gap-1) suffix (by omega)
  have hr : silentSegment machine (cfg 31 (gap-1) (after base gap suffix))
      (cfg (if base (gap-1) then 30 else 18) gap (after base gap suffix)) 1 := by
    apply oneSeg machine
    have ht := return_step (gap-1) (after base gap suffix)
    simpa only [hv, sub_add_cancel] using ht
  have h := segAdd machine _ _ _ (2*suffix.length+3) 1 hs hr
  simpa [Nat.add_assoc] using h

theorem duration_positive (x : Nat) (xs : List Nat) :
    0 < 2 * (UnaryBank.encode (x::xs)).length + 4 := by omega

theorem suffix_shift_and_return_no_beep (base : Int → Bool) (gap : Int)
    (x : Nat) (xs : List Nat) (j : Nat)
    (hj : j < 2 * (UnaryBank.encode (x::xs)).length + 4) :
    ¬ machine.system.BeepFrom
      (cfg 32 (gap+2) (before base gap (UnaryBank.encode (x::xs)))) j :=
  silent_no_beep machine _ _ _ j (suffix_shift_and_return base gap x xs) hj

end Shared.Beeping.NPcoNP.NativeHalfCycleReturn
