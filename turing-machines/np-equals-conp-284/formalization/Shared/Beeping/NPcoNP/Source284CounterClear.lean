import Shared.Beeping.NPcoNP.Source284CounterExtend

/-! Clear a finite unary-marked segment on the actual source tape. The input
counter's terminator and its boundary are already zero; the return scan
rewrites each intervening one to zero. The arbitrary higher suffix and the
entire opposite tape half are preserved. This is one paid source component,
not a construction of the counter or a complete verifier compiler. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284CounterClear

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284CounterExtend (ones counter_ones)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨false,false,some 1⟩
  else if q = 1 then ⟨b,!b,some (if b then 1 else 2)⟩
  else if q = 2 then ⟨false,false,some (if b then 2 else 3)⟩
  else if q = 3 then ⟨b,true,some 4⟩
  else shiftRow 4 (continuation (q-4) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (4+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hsmall : q < 4
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have he : (shiftRow 4 (continuation (q-4) b)).next = some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega,
        show q ≠ 2 by omega,show q ≠ 3 by omega] using hnext
    cases hh : (continuation (q-4) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hv (q-4) (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (4+q) b = shiftRow 4 (continuation q b) := by
  simp [table,show 4+q ≠ 1 by omega,show 4+q ≠ 2 by omega,
    show 4+q ≠ 3 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 4 c) = shiftConfig 4 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 4 c) fuel = shiftConfig 4 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

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

theorem turn_at_end (continuation : Nat → Bool → Row) (left higher : Nat) :
    step (table continuation) ⟨left,2*higher,some 1⟩ = ⟨2*higher,left,some 2⟩ := by
  simp [step,table,bit,Nat.testBit_zero]

theorem erase_one (continuation : Nat → Bool → Row) (left rest : Nat) :
    step (table continuation) ⟨left,2*rest+1,some 2⟩ = ⟨2*left,rest,some 2⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem erase_marks (continuation : Nat → Bool → Row) (n left boundary : Nat) :
    run (table continuation) ⟨left,ones n boundary,some 2⟩ n =
      ⟨2^n*left,boundary,some 2⟩ := by
  induction n generalizing left boundary with
  | zero => simp [run,ones]
  | succ n ih =>
    rw [Source284CounterExtend.ones_succ_right,run_front,erase_one,ih]
    congr 1
    simp [pow_succ]
    ring

theorem leave (continuation : Nat → Bool → Row) (left boundary : Nat) :
    run (table continuation) ⟨left,2*boundary,some 2⟩ 2 =
      ⟨boundary,2*left,some 4⟩ := by
  simp [run,step,table,bit,Nat.testBit_zero] <;> split_ifs <;> omega

/-- The finite prefix clears exactly the boundary, all `n` marks, and the
terminator, without making any assumption on bits above the terminator. -/
theorem clear (continuation : Nat → Bool → Row) (n left higher : Nat) :
    run (table continuation) ⟨left,2*counter n higher,some 0⟩ (2*n+4) =
      ⟨left,2^(n+2)*higher,some 4⟩ := by
  have ht : 2*n+4 = 1+(n+(1+(n+2))) := by omega
  rw [ht,Source284PayloadPop.run_add]
  change run (table continuation) (step (table continuation)
    ⟨left,2*counter n higher,some 0⟩) _ = _
  rw [enter,Source284PayloadPop.run_add,scan_counter,
    Source284PayloadPop.run_add]
  change run (table continuation) (step (table continuation)
    ⟨ones n (2*left),2*higher,some 1⟩) _ = _
  rw [turn_at_end,Source284PayloadPop.run_add,erase_marks,leave]
  congr 1
  simp [pow_add]
  ring

theorem clear_then (continuation : Nat → Bool → Row) (n left higher fuel : Nat) :
    run (table continuation) ⟨left,2*counter n higher,some 0⟩ (2*n+4+fuel) =
      shiftConfig 4 (run continuation ⟨left,2^(n+2)*higher,some 0⟩ fuel) := by
  rw [Source284PayloadPop.run_add,clear]
  change run (table continuation)
    (shiftConfig 4 ⟨left,2^(n+2)*higher,some 0⟩) fuel = _
  exact relocated_run continuation _ fuel

theorem source_clear_then (states : Nat) (continuation : Nat → Bool → Row)
    (n left higher fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (4+states) (table continuation) 1)
      (Source284Relative.initial (2*counter n higher) left) (2*n+4+fuel) =
      Source284SourceRelocation.lift 4
        (Source284Relative.run (encode states continuation 1)
          ⟨left,2^(n+2)*higher,active 0⟩ fuel) := by
  let start : Config := ⟨left,2*counter n higher,some 0⟩
  have hvalid : Valid (4+states) start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource (4+states) (table continuation) 1 start (closed states continuation hn hv)
    hvalid (2*n+4+fuel)
  rw [clear_then,← Source284SourceRelocation.lift_toSource] at hr
  let finish : Config := ⟨left,2^(n+2)*higher,some 0⟩
  have hf : Valid states finish := by intro q hq; simp [finish] at hq; subst q; exact hn
  have hs := run_toSource states continuation 1 finish hv hf fuel
  rw [← hs] at hr
  exact hr

namespace Fixtures

def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
example : run (table loop) ⟨7,2*counter 0 5,some 0⟩ 4 = ⟨7,20,some 4⟩ := by decide +kernel
example : run (table loop) ⟨7,2*counter 3 5,some 0⟩ 10 = ⟨7,160,some 4⟩ := by decide +kernel
example : run (table loop) ⟨0,2*counter 3 0,some 0⟩ 10 = ⟨0,0,some 4⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284CounterClear
