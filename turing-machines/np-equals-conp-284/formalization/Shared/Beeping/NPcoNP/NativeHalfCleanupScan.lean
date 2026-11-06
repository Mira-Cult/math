import Shared.Beeping.NPcoNP.NativeHalfZeroPrefix

/-! Literal states 18/19 scan right to the first double zero, silently and
without changing tape. This is only the forward scan of inherited decrement;
the subsequent rewrite, return path and complete HALF remain separate. -/
namespace Shared.Beeping.NPcoNP.NativeHalfCleanupScan
open Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.UnarySuffixShift

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem row18_zero : machine.table.row 18 false = ⟨false, .right, 19, false⟩ := by decide
theorem row18_one : machine.table.row 18 true = ⟨true, .right, 18, false⟩ := by decide
theorem row19_zero : machine.table.row 19 false = ⟨false, .left, 20, false⟩ := by decide
theorem row19_one : machine.table.row 19 true = ⟨true, .right, 18, false⟩ := by decide

theorem step18_zero (h : Int) (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg 18 h t) = (cfg 19 (h+1) t, false) := by
  have hw : (⟨18, h, t⟩ : Config 284).write false = t := by rw [← ht]; exact write_current _
  simp [cfg, Machine.step, ht, row18_zero, Move.apply, hw]
theorem step18_one (h : Int) (t : Int → Bool) (ht : t h = true) :
    machine.step (cfg 18 h t) = (cfg 18 (h+1) t, false) := by
  have hw : (⟨18, h, t⟩ : Config 284).write true = t := by rw [← ht]; exact write_current _
  simp [cfg, Machine.step, ht, row18_one, Move.apply, hw]
theorem step19_zero (h : Int) (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg 19 h t) = (cfg 20 (h-1) t, false) := by
  have hw : (⟨19, h, t⟩ : Config 284).write false = t := by rw [← ht]; exact write_current _
  simp [cfg, Machine.step, ht, row19_zero, Move.apply, hw]
theorem step19_one (h : Int) (t : Int → Bool) (ht : t h = true) :
    machine.step (cfg 19 h t) = (cfg 18 (h+1) t, false) := by
  have hw : (⟨19, h, t⟩ : Config 284).write true = t := by rw [← ht]; exact write_current _
  simp [cfg, Machine.step, ht, row19_one, Move.apply, hw]

/-- Any prepared prefix containing no double zero is traversed in finite
positive time. Tape and ordered event word are exactly preserved. -/
theorem scan18 (xs : List Bool) (hx : Prefix xs) (h : Int)
    (t : Int → Bool) (hm : Holds t h (xs ++ [false,false])) :
    silentSegment machine (cfg 18 h t) (cfg 20 (h + xs.length) t) (xs.length+2) :=
  scan machine 18 19 20 step18_one step18_zero step19_one step19_zero xs hx h t hm

theorem prefix_zero_encoded (values : List Nat) :
    Prefix (false :: UnaryBank.encode values ++ [true]) := by
  induction values with
  | nil => exact .zeroOne .nil
  | cons x xs ih =>
    simp only [UnaryBank.encode, UnaryBank.block, List.replicate_succ, List.cons_append,
      List.append_assoc]
    exact Prefix.zeroOne (prefix_append (prefix_ones x) ih)

theorem holds_after_suffix (base : Int → Bool) (gap : Int) (suffix : List Bool) :
    Holds (after base gap suffix) (gap+1) (suffix ++ [true,false,false]) := by
  apply holds_of_get
  intro i hi
  by_cases h : i < suffix.length
  · rw [List.getElem_append_left h]
    rw [after_suffix_bit base gap suffix i h]
    simp [bitAt, List.getElem?_eq_getElem h]
  · have hle : i < suffix.length + 3 := by simpa using hi
    have hc : i = suffix.length ∨ i = suffix.length + 1 ∨ i = suffix.length + 2 := by omega
    rcases hc with h0 | h1 | h2
    · subst i
      simpa using (appended_zero_block base gap suffix).1
    · subst i
      have he : gap+1+((suffix.length+1 : Nat) : Int) = gap+2+(suffix.length : Int) := by omega
      rw [he]
      simpa using (appended_zero_block base gap suffix).2
    · subst i
      have ht := after_tail_zero base gap (gap+1+((suffix.length+2 : Nat) : Int)) suffix (by omega)
      simpa [Int.add_assoc] using ht

/-- Following the m=2 suffix shift, scan the exact zero-prefixed bank and
new reserve to its final double zero. This assumes the prepared state-18
configuration; it does not assert its reachability. -/
theorem scan_after_zero_prefix (base : Int → Bool) (gap : Int) (values : List Nat) :
    let full := false :: UnaryBank.encode values
    let pre := full ++ [true]
    silentSegment machine (cfg 18 (gap+1) (after base gap full))
      (cfg 20 (gap+1+pre.length) (after base gap full)) (pre.length+2) := by
  dsimp only
  have hp := prefix_zero_encoded values
  have hh := holds_after_suffix base gap (false :: UnaryBank.encode values)
  apply scan18 _ hp
  simpa [List.append_assoc] using hh

theorem scan_after_zero_prefix_positive (values : List Nat) :
    0 < ((false :: UnaryBank.encode values) ++ [true]).length + 2 := by omega

theorem scan_after_zero_prefix_no_beep (base : Int → Bool) (gap : Int)
    (values : List Nat) (j : Nat)
    (hj : j < ((false :: UnaryBank.encode values) ++ [true]).length + 2) :
    ¬ machine.system.BeepFrom
      (cfg 18 (gap+1) (after base gap (false :: UnaryBank.encode values))) j :=
  silent_no_beep machine _ _ _ j (scan_after_zero_prefix base gap values) hj

end Shared.Beeping.NPcoNP.NativeHalfCleanupScan
