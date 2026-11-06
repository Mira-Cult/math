import Shared.Beeping.NPcoNP.Source284EncoderMarkerSeed

/-! A finite relative source table reads one input bit, turns, and writes the
corresponding fixed codeword over arbitrary target cells. The source bit and
higher source suffix are preserved. The two branch continuations occupy
separate finite ranges; no global suffix clearing is claimed. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284SelectOverwrite

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig offset)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284EncoderMarkerSeed (shift_add)

def falseSize (zero : List Bool) (states : Nat) : Nat := offset zero + states
def trueStart (zero : List Bool) (states : Nat) : Nat := 1 + falseSize zero states
def total (zero one : List Bool) (states : Nat) : Nat :=
  trueStart zero states + (offset one + states)

def table (zero one : List Bool) (states : Nat) (continuation : Nat → Bool → Row)
    (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some (if b then trueStart zero states else 1)⟩
  else if q < trueStart zero states then
    shiftRow 1 (Source284HardwireTable.table zero continuation (q-1) b)
  else shiftRow (trueStart zero states)
    (Source284HardwireTable.table one continuation (q-trueStart zero states) b)

theorem closed (zero one : List Bool) (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (total zero one states) (table zero one states continuation) := by
  intro q hq b q' hnext
  by_cases hz : q = 0
  · subst q; cases b <;> simp [table] at hnext <;> subst q' <;>
      simp [total,trueStart,falseSize,offset] <;> omega
  · by_cases hf : q < trueStart zero states
    · have hc := Source284HardwireTable.closed zero continuation states hn hv
      have hq0 : q-1 < offset zero+states := by dsimp [trueStart,falseSize] at hf; omega
      have ht : (shiftRow 1 (Source284HardwireTable.table zero continuation (q-1) b)).next = some q' := by
        simpa [table,hz,hf] using hnext
      cases he : (Source284HardwireTable.table zero continuation (q-1) b).next with
      | none => simp [shiftRow,he] at ht
      | some r =>
        have h := hc (q-1) hq0 b r he
        simp [shiftRow,he] at ht
        subst q'; dsimp [trueStart,total,falseSize] at *; omega
    · have hc := Source284HardwireTable.closed one continuation states hn hv
      have hq0 : q-trueStart zero states < offset one+states := by dsimp [total] at hq; omega
      have ht : (shiftRow (trueStart zero states)
          (Source284HardwireTable.table one continuation (q-trueStart zero states) b)).next = some q' := by
        simpa [table,hz,hf] using hnext
      cases he : (Source284HardwireTable.table one continuation (q-trueStart zero states) b).next with
      | none => simp [shiftRow,he] at ht
      | some r =>
        have h := hc (q-trueStart zero states) hq0 b r he
        simp [shiftRow,he] at ht
        subst q'; dsimp [total] at *; omega

theorem choose_step (zero one : List Bool) (states : Nat) (continuation : Nat → Bool → Row)
    (left tail : Nat) (b : Bool) :
    step (table zero one states continuation) ⟨left,2*tail+bit b,some 0⟩ =
      ⟨2*tail+bit b,left,some (if b then trueStart zero states else 1)⟩ := by
  cases b <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod] <;> omega

theorem false_relocated_step (zero one : List Bool) (states : Nat)
    (continuation : Nat → Bool → Row) (c : Config) (hc : Valid (falseSize zero states) c) :
    step (table zero one states continuation) (shiftConfig 1 c) =
      shiftConfig 1 (step (Source284HardwireTable.table zero continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      have hq : q < falseSize zero states := hc q rfl
      have hlt : 1+q < trueStart zero states := by dsimp [trueStart]; omega
      simp only [shiftConfig,Option.map_some,step,table,show 1+q ≠ 0 by omega,
        ↓reduceIte,hlt,show 1+q-1=q by omega,shiftRow]
      split <;> rfl

theorem false_relocated_run (zero one : List Bool) (states : Nat)
    (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation)
    (c : Config) (hc : Valid (falseSize zero states) c) (fuel : Nat) :
    run (table zero one states continuation) (shiftConfig 1 c) fuel =
      shiftConfig 1 (run (Source284HardwireTable.table zero continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    simp only [run,ih]
    apply false_relocated_step
    exact valid_run _ _ _ (Source284HardwireTable.closed zero continuation states hn hv) hc fuel

theorem true_relocated_step (zero one : List Bool) (states : Nat)
    (continuation : Nat → Bool → Row) (c : Config) :
    step (table zero one states continuation) (shiftConfig (trueStart zero states) c) =
      shiftConfig (trueStart zero states) (step (Source284HardwireTable.table one continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      have hp : 0 < trueStart zero states := by simp [trueStart,falseSize]
      have he : trueStart zero states+q ≠ 0 := by omega
      have hn : ¬ trueStart zero states+q < trueStart zero states := by omega
      simp only [shiftConfig,Option.map_some,step,table,he,↓reduceIte,hn,
        show trueStart zero states+q-trueStart zero states=q by omega,shiftRow]
      split <;> rfl

theorem true_relocated_run (zero one : List Bool) (states : Nat)
    (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table zero one states continuation) (shiftConfig (trueStart zero states) c) fuel =
      shiftConfig (trueStart zero states) (run (Source284HardwireTable.table one continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,true_relocated_step]

/-- One bit is selected in one transition; the appropriate writer then
executes for its exact allocated cost and the continuation is followed. -/
theorem select_then (zero one : List Bool) (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) (left tail fuel : Nat) (b : Bool) :
    let word := if b then one else zero
    let start := if b then trueStart zero states else 1
    run (table zero one states continuation) ⟨left,2*tail+bit b,some 0⟩
      (1+offset word+fuel) =
      shiftConfig (start+offset word) (run continuation
        ⟨2*tail+bit b,stack word (2*(left/2^(word.length+1))),some 0⟩ fuel) := by
  cases b with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte]
    rw [show 1+offset zero+fuel = (offset zero+fuel)+1 by omega,
      Source284HardwireTable.run_front,choose_step]
    change run (table zero one states continuation) (shiftConfig 1 ⟨2*tail+bit false,left,some 0⟩) _ = _
    have hc : Valid (falseSize zero states) ⟨2*tail+bit false,left,some 0⟩ := by
      intro q hq; simp at hq; subst q; simp [falseSize,offset]
    rw [false_relocated_run zero one states continuation hn hv _ hc,
      Source284HardwireOverwrite.overwrite_then,shift_add]
  | true =>
    simp only [↓reduceIte]
    rw [show 1+offset one+fuel = (offset one+fuel)+1 by omega,
      Source284HardwireTable.run_front,choose_step]
    change run (table zero one states continuation)
      (shiftConfig (trueStart zero states) ⟨2*tail+bit true,left,some 0⟩) _ = _
    rw [true_relocated_run,Source284HardwireOverwrite.overwrite_then,shift_add]

end Shared.Beeping.NPcoNP.Source284SelectOverwrite
