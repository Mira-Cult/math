import Shared.Beeping.NPcoNP.Source284PayloadSentinel

/-! A finite pass removes the extra false/one payload sentinel by clearing
its marker, then returns to the original boundary. The former `00` terminator
and all higher suffix bits remain explicitly represented. -/
namespace Shared.Beeping.NPcoNP.Source284DropPayloadSentinel

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (push flipped)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add push_snoc)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else if q = 2 then ⟨b,!b,some (if b then 1 else 3)⟩
  else if q = 3 then ⟨b,false,some 4⟩
  else if q = 4 then ⟨false,false,some 5⟩
  else if q = 5 then ⟨b,false,some 9⟩
  else shiftRow 6 (Source284ScratchFlipReturn.table continuation (q-6) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (12+states) (table continuation) := by
  have hc := Source284ScratchFlipReturn.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases hsmall : q < 6
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have h0 : q ≠ 0 := by omega
    have h1 : q ≠ 1 := by omega
    have h2 : q ≠ 2 := by omega
    have h3 : q ≠ 3 := by omega
    have h4 : q ≠ 4 := by omega
    have h5 : q ≠ 5 := by omega
    have ht : (shiftRow 6 (Source284ScratchFlipReturn.table continuation (q-6) b)).next = some q' := by
      simpa [table,h0,h1,h2,h3,h4,h5] using hnext
    have hq0 : q-6 < 6+states := by omega
    cases he : (Source284ScratchFlipReturn.table continuation (q-6) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hc (q-6) hq0 b r he
      simp [shiftRow,he] at ht
      subst q'
      omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (6+q) b = shiftRow 6 (Source284ScratchFlipReturn.table continuation q b) := by
  have h0 : 6+q ≠ 0 := by omega
  have h1 : 6+q ≠ 1 := by omega
  have h2 : 6+q ≠ 2 := by omega
  have h3 : 6+q ≠ 3 := by omega
  have h4 : 6+q ≠ 4 := by omega
  have h5 : 6+q ≠ 5 := by omega
  simp [table,h0,h1,h2,h3,h4,h5]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 6 c) =
      shiftConfig 6 (step (Source284ScratchFlipReturn.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 6 c) fuel =
      shiftConfig 6 (run (Source284ScratchFlipReturn.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem startup (continuation : Nat → Bool → Row) (left stream : Nat) :
    step (table continuation) ⟨left,2*stream,some 0⟩ = ⟨2*left,stream,some 1⟩ := by
  simp [step,table,bit,Nat.testBit_zero]

theorem forward_pair (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    run (table continuation) ⟨left,bit b+2+4*tail,some 1⟩ 2 =
      ⟨4*left+2*bit b+1,tail,some 1⟩ := by
  have h1 : step (table continuation) ⟨left,bit b+2+4*tail,some 1⟩ =
      ⟨2*left+bit b,1+2*tail,some 2⟩ := by
    cases b <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h2 : step (table continuation) ⟨2*left+bit b,1+2*tail,some 2⟩ =
      ⟨4*left+2*bit b+1,tail,some 1⟩ := by
    cases b <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  rw [run_front,h1,run_front,h2]
  rfl

theorem scan (continuation : Nat → Bool → Row) (w : List Bool) (left tail : Nat) :
    run (table continuation) ⟨left,flipped w tail,some 1⟩ (2*w.length) =
      ⟨push left w,4*tail,some 1⟩ := by
  induction w generalizing left with
  | nil => simp [flipped,push,run]
  | cons b bs ih =>
    have ht : 2*(b::bs).length = 2+2*bs.length := by simp; omega
    rw [ht,run_add]
    simp only [flipped,push]
    rw [forward_pair,ih]

/-- After scanning the appended sentinel, inspect the terminator, turn back,
clear the sentinel marker, and enter the existing reverse scanner. -/
theorem remove_end (continuation : Nat → Bool → Row) (left tail : Nat) :
    run (table continuation) ⟨4*left+1,4*tail,some 1⟩ 5 =
      shiftConfig 6 ⟨16*tail,left,some 3⟩ := by
  have h1 : step (table continuation) ⟨4*left+1,4*tail,some 1⟩ =
      ⟨2*(4*left+1),2*tail,some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero]
    omega
  have h2 : step (table continuation) ⟨2*(4*left+1),2*tail,some 2⟩ =
      ⟨2*tail,2*(4*left+1),some 3⟩ := by
    simp [step,table,bit,Nat.testBit_zero]
  have h3 : step (table continuation) ⟨2*tail,2*(4*left+1),some 3⟩ =
      ⟨4*tail,4*left+1,some 4⟩ := by
    simp [step,table,bit,Nat.testBit_zero]
    omega
  have h4 : step (table continuation) ⟨4*tail,4*left+1,some 4⟩ =
      ⟨8*tail,2*left,some 5⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
    all_goals repeat' constructor
    all_goals omega
  have h5 : step (table continuation) ⟨8*tail,2*left,some 5⟩ =
      ⟨16*tail,left,some 9⟩ := by
    simp [step,table,bit,Nat.testBit_zero]
    omega
  rw [run_front,h1,run_front,h2,run_front,h3,run_front,h4,run_front,h5]
  rfl

/-- The sentinel is removed in exactly `4*n+10` steps, and the entire
left tape and payload are restored. The new suffix is `4*tail`. -/
theorem drop (continuation : Nat → Bool → Row) (w : List Bool) (left tail : Nat) :
    run (table continuation) ⟨left,2*flipped (w++[false]) tail,some 0⟩ (4*w.length+10) =
      ⟨left,2*flipped w (4*tail),some 12⟩ := by
  have ht : 4*w.length+10 = 1+(2*(w++[false]).length+(5+(2*w.length+2))) := by simp; omega
  rw [ht,run_add _ _ 1 (2*(w++[false]).length+(5+(2*w.length+2)))]
  change run (table continuation) (step (table continuation)
    ⟨left,2*flipped (w++[false]) tail,some 0⟩) _ = _
  rw [startup,run_add _ _ (2*(w++[false]).length) (5+(2*w.length+2)),scan,push_snoc]
  simp only [bit,Bool.false_eq_true,if_false,zero_mul,add_zero]
  rw [run_add _ _ 5 (2*w.length+2),remove_end,relocated_run]
  have ht' : 2*w.length+2 = 2*w.length+2 := rfl
  rw [ht',Source284ScratchFlipReturn.run_add,Source284ScratchFlipReturn.reverse_pairs]
  have he : 16*tail = 4*(4*tail) := by omega
  rw [he,Source284ScratchFlipReturn.raw_flipped,Source284ScratchFlipReturn.finish]
  rfl

end Shared.Beeping.NPcoNP.Source284DropPayloadSentinel
