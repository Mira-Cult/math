import Shared.Beeping.NPcoNP.Source284ScratchFlip

/-! An actual finite reverse pass for the flipped scratch stream. It detects
the original zero boundary, restores the certificate half, and enters a
finite continuation with payload/one pairs followed by a zero/zero terminator.
No source-level canonical pair or witness conversion is claimed. -/
namespace Shared.Beeping.NPcoNP.Source284ScratchFlipReturn

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (push flipped)

/-- Reverse from the high terminator, read marker/data pairs until the zero
boundary, then turn back from the certificate to the original head position. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else if q = 2 then ⟨b,false,some 3⟩
  else if q = 3 then ⟨b,false,some (if b then 4 else 5)⟩
  else if q = 4 then ⟨b,false,some 3⟩
  else if q = 5 then ⟨b,true,some 6⟩
  else shiftRow 6 (continuation (q-6) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (6+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; simp [table] at hnext; omega
  · by_cases h1 : q = 1
    · subst q; simp [table] at hnext; omega
    · by_cases h2 : q = 2
      · subst q; simp [table] at hnext; omega
      · by_cases h3 : q = 3
        · subst q; cases b <;> simp [table] at hnext <;> omega
        · by_cases h4 : q = 4
          · subst q; simp [table] at hnext; omega
          · by_cases h5 : q = 5
            · subst q; simp [table] at hnext; omega
            · have ht : (shiftRow 6 (continuation (q-6) b)).next = some q' := by
                simpa [table,h0,h1,h2,h3,h4,h5] using hnext
              have hq0 : q-6 < states := by omega
              cases he : (continuation (q-6) b).next with
              | none => simp [shiftRow,he] at ht
              | some r =>
                have h := hv (q-6) hq0 b r he
                simp [shiftRow,he] at ht
                subst q'
                omega

theorem run_add (t : Nat → Bool → Row) (c : Config) (a b : Nat) :
    run t c (a+b) = run t (run t c a) b := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    change step t (run t c (a+b)) = step t (run t (run t c a) b)
    rw [ih]

theorem push_append (left : Nat) (xs ys : List Bool) :
    push left (xs++ys) = push (push left xs) ys := by
  induction xs generalizing left with
  | nil => rfl
  | cons b bs ih => simpa [push] using ih (4*left+2*bit b+1)

theorem push_snoc (left : Nat) (xs : List Bool) (b : Bool) :
    push left (xs++[b]) = 4*push left xs+2*bit b+1 := by
  rw [push_append]
  rfl

def raw : List Bool → Nat → Nat
  | [], tail => tail
  | b::bs, tail => bit b+2+4*raw bs tail

theorem raw_append (xs ys : List Bool) (tail : Nat) :
    raw (xs++ys) tail = raw xs (raw ys tail) := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [raw,ih]

theorem raw_flipped (w : List Bool) (tail : Nat) : raw w (4*tail) = flipped w tail := by
  induction w with
  | nil => rfl
  | cons b bs ih => simp [raw,flipped,ih]

theorem turn_start (continuation : Nat → Bool → Row) (left right : Nat) :
    run (table continuation) ⟨4*left,right,some 0⟩ 3 = ⟨4*right,left,some 3⟩ := by
  simp [run,step,table,bit,Nat.testBit_zero]
  try split_ifs
  all_goals repeat' constructor
  all_goals omega

theorem reverse_pair (continuation : Nat → Bool → Row) (left right : Nat) (b : Bool) :
    run (table continuation) ⟨left,4*right+2*bit b+1,some 3⟩ 2 =
      ⟨4*left+2+bit b,right,some 3⟩ := by
  cases b <;> simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;>
    congr 1 <;> try split_ifs
  all_goals repeat' constructor
  all_goals omega

theorem reverse_pairs (continuation : Nat → Bool → Row) (w : List Bool) (left right : Nat) :
    run (table continuation) ⟨left,push right w,some 3⟩ (2*w.length) =
      ⟨raw w left,right,some 3⟩ := by
  induction w using List.reverseRecOn generalizing left with
  | nil => simp [run,push,raw]
  | append_singleton w b ih =>
    rw [push_snoc]
    have ht : 2*(w++[b]).length = 2+2*w.length := by simp; omega
    rw [ht,run_add,reverse_pair,ih,raw_append]
    simp [raw]
    congr 1
    ring

theorem finish (continuation : Nat → Bool → Row) (left certificate : Nat) :
    run (table continuation) ⟨left,2*certificate,some 3⟩ 2 =
      ⟨certificate,2*left,some 6⟩ := by
  simp [run,step,table,bit,Nat.testBit_zero]
  try split_ifs
  all_goals repeat' constructor
  all_goals omega

/-- A self-delimiting reverse pass returns to the original head position,
with the whole certificate and the marker-flipped scratch stream. -/
theorem return_frame (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail : Nat) :
    run (table continuation) ⟨4*push (2*certificate) w,tail,some 0⟩ (2*w.length+5) =
      ⟨certificate,2*flipped w tail,some 6⟩ := by
  have ht : 2*w.length+5 = 3+(2*w.length)+2 := by omega
  rw [ht,run_add,run_add,turn_start,reverse_pairs,raw_flipped,finish]

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (6+q) b = shiftRow 6 (continuation q b) := by
  have h0 : 6+q ≠ 0 := by omega
  have h1 : 6+q ≠ 1 := by omega
  have h2 : 6+q ≠ 2 := by omega
  have h3 : 6+q ≠ 3 := by omega
  have h4 : 6+q ≠ 4 := by omega
  have h5 : 6+q ≠ 5 := by omega
  simp [table,h0,h1,h2,h3,h4,h5]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 6 c) = shiftConfig 6 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table continuation) (shiftConfig 6 c) clock = shiftConfig 6 (run continuation c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

end Shared.Beeping.NPcoNP.Source284ScratchFlipReturn
