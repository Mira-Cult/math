import Shared.Beeping.NPcoNP.Source284ScratchFlipReturn

/-! Install a distinguished end pair after the flipped payload. The added
false pair is a sentinel, not a payload bit. The installation overwrites two
bits of the unused high suffix and restores the certificate. -/
namespace Shared.Beeping.NPcoNP.Source284PayloadSentinel

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (push flipped)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add push_snoc)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 1⟩
  else if q = 1 then ⟨b,false,some (2+bit b)⟩
  else if q = 2 then ⟨true,false,some (if b then 1 else 4)⟩
  else if q = 3 then ⟨b,false,some (if b then 1 else 6)⟩
  else if q = 4 then ⟨false,false,some 5⟩
  else if q = 5 then ⟨false,false,some 7⟩
  else if q = 6 then ⟨b,false,some 6⟩
  else shiftRow 7 (Source284ScratchFlipReturn.table continuation (q-7) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (13+states) (table continuation) := by
  have hc := Source284ScratchFlipReturn.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; simp [table] at hnext; omega
  · by_cases h1 : q = 1
    · subst q; cases b <;> simp [table,bit] at hnext <;> omega
    · by_cases h2 : q = 2
      · subst q; cases b <;> simp [table] at hnext <;> omega
      · by_cases h3 : q = 3
        · subst q; cases b <;> simp [table] at hnext <;> omega
        · by_cases h4 : q = 4
          · subst q; simp [table] at hnext; omega
          · by_cases h5 : q = 5
            · subst q; simp [table] at hnext; omega
            · by_cases h6 : q = 6
              · subst q; simp [table] at hnext; omega
              · have ht : (shiftRow 7 (Source284ScratchFlipReturn.table continuation (q-7) b)).next = some q' := by
                  simpa [table,h0,h1,h2,h3,h4,h5,h6] using hnext
                have hq0 : q-7 < 6+states := by omega
                cases he : (Source284ScratchFlipReturn.table continuation (q-7) b).next with
                | none => simp [shiftRow,he] at ht
                | some r =>
                  have h := hc (q-7) hq0 b r he
                  simp [shiftRow,he] at ht
                  subst q'
                  omega

theorem start (continuation : Nat → Bool → Row) (left right : Nat) :
    run (table continuation) ⟨left,2*right,some 0⟩ 1 = ⟨2*left,right,some 1⟩ := by
  simp [run,step,table,bit,Nat.testBit_zero]
  all_goals repeat' constructor
  all_goals omega

theorem data_pair (continuation : Nat → Bool → Row) (left right : Nat) (b : Bool) :
    run (table continuation) ⟨left,bit b+2+4*right,some 1⟩ 2 =
      ⟨4*left+2*bit b+1,right,some 1⟩ := by
  cases b <;> simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;>
    congr 1 <;> try split_ifs
  all_goals repeat' constructor
  all_goals omega

theorem scan (continuation : Nat → Bool → Row) (w : List Bool) (left tail : Nat) :
    run (table continuation) ⟨left,flipped w tail,some 1⟩ (2*w.length) =
      ⟨push left w,4*tail,some 1⟩ := by
  induction w generalizing left with
  | nil => simp [run,flipped,push]
  | cons b bs ih =>
    have ht : 2*(b::bs).length = 2+2*bs.length := by simp; omega
    rw [ht,run_add]
    simp only [flipped,push]
    rw [data_pair,ih]

theorem install_end (continuation : Nat → Bool → Row) (left tail : Nat) :
    run (table continuation) ⟨left,4*tail,some 1⟩ 4 =
      shiftConfig 7 ⟨4*(4*left+1),tail/4,some 0⟩ := by
  have h1 : step (table continuation) ⟨left,4*tail,some 1⟩ = ⟨2*left,2*tail,some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero]
    all_goals congr 1 <;> omega
  have h2 : step (table continuation) ⟨2*left,2*tail,some 2⟩ = ⟨4*left+1,tail,some 4⟩ := by
    simp [step,table,bit,Nat.testBit_zero]
    all_goals omega
  have h3 : step (table continuation) ⟨4*left+1,tail,some 4⟩ =
      ⟨2*(4*left+1),tail/2,some 5⟩ := by
    simp [step,table,bit,Nat.testBit_zero]
  have h4 : step (table continuation) ⟨2*(4*left+1),tail/2,some 5⟩ =
      ⟨4*(4*left+1),(tail/2)/2,some 7⟩ := by
    simp [step,table,bit,Nat.testBit_zero]
    all_goals omega
  change step (table continuation) (step (table continuation) (step (table continuation)
    (step (table continuation) ⟨left,4*tail,some 1⟩))) = _
  rw [h1,h2,h3,h4,Nat.div_div_eq_div_mul]
  rfl

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (7+q) b = shiftRow 7 (Source284ScratchFlipReturn.table continuation q b) := by
  have h0 : 7+q ≠ 0 := by omega
  have h1 : 7+q ≠ 1 := by omega
  have h2 : 7+q ≠ 2 := by omega
  have h3 : 7+q ≠ 3 := by omega
  have h4 : 7+q ≠ 4 := by omega
  have h5 : 7+q ≠ 5 := by omega
  have h6 : 7+q ≠ 6 := by omega
  simp [table,h0,h1,h2,h3,h4,h5,h6]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 7 c) =
      shiftConfig 7 (step (Source284ScratchFlipReturn.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table continuation) (shiftConfig 7 c) clock =
      shiftConfig 7 (run (Source284ScratchFlipReturn.table continuation) c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

/-- Installs a sentinel pair and returns to the original boundary. -/
theorem install (continuation : Nat → Bool → Row) (w : List Bool) (certificate tail : Nat) :
    run (table continuation) ⟨certificate,2*flipped w tail,some 0⟩ (4*w.length+12) =
      ⟨certificate,2*flipped (w++[false]) (tail/4),some 13⟩ := by
  have ht : 4*w.length+12 = 1+(2*w.length+(4+(2*(w++[false]).length+5))) := by simp; omega
  rw [ht,run_add,start,run_add,scan,run_add,install_end]
  have hp : push (2*certificate) (w++[false]) = 4*push (2*certificate) w+1 := by
    simp [push_snoc,bit]
  rw [← hp,relocated_run,Source284ScratchFlipReturn.return_frame]
  rfl

end Shared.Beeping.NPcoNP.Source284PayloadSentinel
