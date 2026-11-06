import Shared.Beeping.NPcoNP.Source284CountedShift
import Shared.Beeping.NPcoNP.Source284SourceRelocation

/-! An explicit finite source prefix extends a unary counter in an ignored
suffix. It preserves the boundary and the complete opposite half, overwrites
one additional high suffix bit, and returns to the boundary before continuing.
Supplying the number of extensions and reaching this boundary are separate
obligations. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284CounterExtend

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)

/-- The zero boundary precedes the unary ones and their zero terminator.
Rows 0--4 scan, append one token, install the new zero, and return. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨false,false,some 1⟩
  else if q = 1 then ⟨true,false,some (if b then 1 else 2)⟩
  else if q = 2 then ⟨false,true,some 3⟩
  else if q = 3 then ⟨b,false,some (if b then 3 else 4)⟩
  else if q = 4 then ⟨b,true,some 5⟩
  else shiftRow 5 (continuation (q-5) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (5+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hsmall : q < 5
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have he : (shiftRow 5 (continuation (q-5) b)).next = some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega,
        show q ≠ 2 by omega,show q ≠ 3 by omega,show q ≠ 4 by omega] using hnext
    cases hh : (continuation (q-5) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hv (q-5) (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (5+q) b = shiftRow 5 (continuation q b) := by
  simp [table,show 5+q ≠ 1 by omega,show 5+q ≠ 2 by omega,
    show 5+q ≠ 3 by omega,show 5+q ≠ 4 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 5 c) = shiftConfig 5 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 5 c) fuel = shiftConfig 5 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

def ones : Nat → Nat → Nat
  | 0, left => left
  | n+1, left => ones n (2*left+1)

theorem ones_succ_right (n left : Nat) : ones (n+1) left = 2*ones n left+1 := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih => simpa only [ones] using ih (2*left+1)

theorem counter_ones (n higher : Nat) : counter n higher = ones n (2*higher) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [counter,ones_succ_right,ih]

theorem enter (continuation : Nat → Bool → Row) (left rest : Nat) :
    step (table continuation) ⟨left,2*rest,some 0⟩ = ⟨2*left,rest,some 1⟩ := by
  simp [step,table,bit,Nat.testBit_zero]

theorem scan_one (continuation : Nat → Bool → Row) (left rest : Nat) :
    step (table continuation) ⟨left,2*rest+1,some 1⟩ = ⟨2*left+1,rest,some 1⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem scan_counter (continuation : Nat → Bool → Row) (n left higher : Nat) :
    run (table continuation) ⟨left,counter n higher,some 1⟩ n =
      ⟨ones n left,2*higher,some 1⟩ := by
  induction n generalizing left with
  | zero => rfl
  | succ n ih =>
    rw [run_front]
    change run (table continuation)
      (step (table continuation) ⟨left,2*counter n higher+1,some 1⟩) n = _
    rw [scan_one,ih]
    rfl

theorem append_and_turn (continuation : Nat → Bool → Row) (left higher : Nat) :
    run (table continuation) ⟨left,2*higher,some 1⟩ 2 =
      ⟨2*(higher/2),2*left+1,some 3⟩ := by
  simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem back_one (continuation : Nat → Bool → Row) (left rest : Nat) :
    step (table continuation) ⟨left,2*rest+1,some 3⟩ = ⟨2*left+1,rest,some 3⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem rewind (continuation : Nat → Bool → Row) (n left boundary : Nat) :
    run (table continuation) ⟨left,ones n boundary,some 3⟩ n =
      ⟨ones n left,boundary,some 3⟩ := by
  induction n generalizing left boundary with
  | zero => rfl
  | succ n ih =>
    rw [ones_succ_right,run_front,back_one,ih]
    rfl

theorem return_boundary (continuation : Nat → Bool → Row) (left boundary : Nat) :
    run (table continuation) ⟨left,2*boundary,some 3⟩ 2 =
      ⟨boundary,2*left,some 5⟩ := by
  simp [run,step,table,bit,Nat.testBit_zero] <;> split_ifs <;> omega

/-- The exact configuration immediately before the final return move. -/
theorem extend_pre (continuation : Nat → Bool → Row) (n left higher : Nat) :
    run (table continuation) ⟨left,2*counter n higher,some 0⟩ (2*n+5) =
      ⟨2*counter (n+1) (higher/2),left,some 4⟩ := by
  have ht : 2*n+5 = 1+(n+(2+((n+1)+1))) := by omega
  rw [ht,Source284PayloadPop.run_add]
  change run (table continuation) (step (table continuation)
    ⟨left,2*counter n higher,some 0⟩) _ = _
  rw [enter,Source284PayloadPop.run_add,scan_counter,
    Source284PayloadPop.run_add,append_and_turn]
  rw [← ones_succ_right]
  rw [Source284PayloadPop.run_add,rewind]
  rw [← counter_ones]
  simp [run,step,table,bit,Nat.testBit_zero]

/-- The local counter grows by one token and its new terminator overwrites
one previously ignored high bit. The complete other tape half is preserved. -/
theorem extend (continuation : Nat → Bool → Row) (n left higher : Nat) :
    run (table continuation) ⟨left,2*counter n higher,some 0⟩ (2*n+6) =
      ⟨left,2*counter (n+1) (higher/2),some 5⟩ := by
  have ht : 2*n+6 = 1+(n+(2+((n+1)+2))) := by omega
  rw [ht,Source284PayloadPop.run_add]
  change run (table continuation) (step (table continuation)
    ⟨left,2*counter n higher,some 0⟩) _ = _
  rw [enter,Source284PayloadPop.run_add,scan_counter,
    Source284PayloadPop.run_add,append_and_turn]
  rw [← ones_succ_right]
  rw [Source284PayloadPop.run_add,rewind,return_boundary]
  rw [← counter_ones]

/-- After the charged extension, every requested continuation step is run
with the actual relocated finite rows. -/
theorem extend_then (continuation : Nat → Bool → Row) (n left higher fuel : Nat) :
    run (table continuation) ⟨left,2*counter n higher,some 0⟩ (2*n+6+fuel) =
      shiftConfig 5 (run continuation ⟨left,2*counter (n+1) (higher/2),some 0⟩ fuel) := by
  rw [Source284PayloadPop.run_add,extend]
  change run (table continuation)
    (shiftConfig 5 ⟨left,2*counter (n+1) (higher/2),some 0⟩) fuel = _
  exact relocated_run continuation _ fuel

/-- The executable unary-record source performs the same finite extension
and its closed continuation. -/
theorem source_extend_then (states : Nat) (continuation : Nat → Bool → Row)
    (n left higher fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (5+states) (table continuation) 1)
      (Source284Relative.initial (2*counter n higher) left) (2*n+6+fuel) =
      Source284SourceRelocation.lift 5
        (Source284Relative.run (encode states continuation 1)
          ⟨left,2*counter (n+1) (higher/2),active 0⟩ fuel) := by
  let start : Config := ⟨left,2*counter n higher,some 0⟩
  have hvalid : Valid (5+states) start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource (5+states) (table continuation) 1 start (closed states continuation hn hv)
    hvalid (2*n+6+fuel)
  rw [extend_then,← Source284SourceRelocation.lift_toSource] at hr
  let finish : Config := ⟨left,2*counter (n+1) (higher/2),some 0⟩
  have hf : Valid states finish := by intro q hq; simp [finish] at hq; subst q; exact hn
  have hs := run_toSource states continuation 1 finish hv hf fuel
  rw [← hs] at hr
  exact hr

namespace Fixtures

def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
example : run (table loop) ⟨7,2*counter 0 5,some 0⟩ 6 =
    ⟨7,2*counter 1 2,some 5⟩ := by decide +kernel
example : run (table loop) ⟨7,2*counter 3 5,some 0⟩ 12 =
    ⟨7,2*counter 4 2,some 5⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284CounterExtend
