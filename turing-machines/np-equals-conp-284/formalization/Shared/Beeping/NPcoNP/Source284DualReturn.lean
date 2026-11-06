import Shared.Beeping.NPcoNP.Source284NestedReturn

/-! Two disjoint copies of the finite inner-block return. Two paid turns
preserve the boundary while dispatching from entry states 0 and 1. Both
outputs are distinct sinks; redirecting them is a later control obligation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284DualReturn

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchScanner (push)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def sink (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
def base := Source284NestedReturn.table sink

def offset (mode : Nat) : Nat := if mode = 0 then 4 else 15

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 2⟩
  else if q = 1 then ⟨b,true,some 3⟩
  else if q = 2 then ⟨b,true,some 4⟩
  else if q = 3 then ⟨b,true,some 15⟩
  else if q < 15 then shiftRow 4 (base (q-4) b)
  else if q < 26 then shiftRow 15 (base (q-15) b)
  else shiftRow 26 (continuation (q-26) b)

theorem base_closed : Closed 11 base := by
  have hs : Closed 1 sink := by intro q hq b q' hnext; simp [sink] at hnext; omega
  simpa [base] using Source284NestedReturn.closed 1 sink (by omega) hs

theorem copy_row (continuation : Nat → Bool → Row) (mode q : Nat) (b : Bool)
    (hm : mode < 2) (hq : q < 11) :
    table continuation (offset mode+q) b = shiftRow (offset mode) (base q b) := by
  interval_cases mode
  · simp [offset,table,show 4+q ≠ 1 by omega,show 4+q ≠ 2 by omega,
      show 4+q ≠ 3 by omega,show 4+q < 15 by omega]
  · simp [offset,table,show 15+q ≠ 1 by omega,show 15+q ≠ 2 by omega,
      show 15+q ≠ 3 by omega,show ¬ 15+q < 15 by omega,show 15+q < 26 by omega]

theorem copy_step (continuation : Nat → Bool → Row) (mode : Nat) (c : Config)
    (hm : mode < 2) (hv : Valid 11 c) :
    step (table continuation) (shiftConfig (offset mode) c) =
      shiftConfig (offset mode) (step base c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      have hq : q < 11 := hv q rfl
      simp only [shiftConfig,Option.map_some,step,copy_row continuation mode q _ hm hq,shiftRow]
      split <;> rfl

theorem copy_run (continuation : Nat → Bool → Row) (mode : Nat) (c : Config)
    (hm : mode < 2) (hv : Valid 11 c) (fuel : Nat) :
    run (table continuation) (shiftConfig (offset mode) c) fuel =
      shiftConfig (offset mode) (run base c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    simp only [run,ih,copy_step continuation mode _ hm (valid_run 11 base c base_closed hv fuel)]

theorem enter (continuation : Nat → Bool → Row) (mode left right : Nat) (hm : mode < 2) :
    run (table continuation) ⟨left,right,some mode⟩ 2 =
      shiftConfig (offset mode) ⟨left,right,some 0⟩ := by
  interval_cases mode <;>
    simp [run,step,table,offset,shiftConfig,bit,Nat.testBit_zero] <;> split_ifs <;> omega

/-- Both exits return the same tape while retaining the branch in control. -/
theorem restore (continuation : Nat → Bool → Row) (mode m outer stream : Nat) (hm : mode < 2) :
    run (table continuation)
      ⟨outer,4*push (2*stream+1) (List.replicate m false),some mode⟩ (2*m+6) =
    ⟨pairTape (List.replicate m false) outer,2*stream,some (offset mode+10)⟩ := by
  have ht : 2*m+6 = 2+(2*m+4) := by omega
  rw [ht,Source284ScratchScanner.run_add,enter _ _ _ _ hm]
  have hv : Valid 11 ⟨outer,4*push (2*stream+1) (List.replicate m false),some 0⟩ := by
    intro q hq; simp at hq; omega
  rw [copy_run _ _ _ hm hv]
  change shiftConfig (offset mode)
    (run (Source284NestedReturn.table sink) ⟨outer,4*push (2*stream+1) (List.replicate m false),some 0⟩ _) = _
  rw [Source284NestedReturn.restore]
  simp [shiftConfig]

/-- The finite prefix is closed, and each output state retains its branch. -/
theorem finite_rows : ∀ q : Fin 26, ∀ b : Bool, (table sink q.val b).next.getD 26 < 26 := by decide +kernel

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (26+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hl : q < 26
  · have he : (table sink q b).next = some q' := by
      simpa [table,show ¬ 26 ≤ q by omega,show q < 26 by omega] using hnext
    have ht := finite_rows ⟨q,hl⟩ b
    simp [he] at ht
    omega
  · have he : (shiftRow 26 (continuation (q-26) b)).next = some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega,show q ≠ 2 by omega,
        show q ≠ 3 by omega,show ¬ q < 15 by omega,show ¬ q < 26 by omega] using hnext
    cases hh : (continuation (q-26) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hv (q-26) (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega

end Shared.Beeping.NPcoNP.Source284DualReturn
