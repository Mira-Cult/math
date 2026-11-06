import Shared.Beeping.NPcoNP.Source284UnaryPairScanner

/-! A finite source table marks the first zero-valued unary pair, or detects
that all pairs are already marked. It restores the input boundary and the
certificate and selects one of two continuation states. This is one operation
for a later length comparator, not a complete comparator or bounded loader. -/
namespace Shared.Beeping.NPcoNP.Source284UnaryMarkOne

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284PayloadLoop (scratch)
open Shared.Beeping.NPcoNP.Source284ScratchScanner (push)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

/-- A one bit marks the protected scratch boundary while the head examines
pairs. Control remembers whether it found a zero token or the sentinel. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨true,true,some 1⟩
  else if q = 1 then ⟨b,false,some (if b then 2 else 3)⟩
  else if q = 2 then ⟨b,false,some 1⟩
  else if q = 3 then ⟨b,true,some (if b then 5 else 4)⟩
  else if q = 4 then ⟨true,false,some 6⟩
  else if q = 5 then ⟨b,false,some 7⟩
  else if q = 6 then ⟨false,b,some (if b then 10 else 8)⟩
  else if q = 7 then ⟨false,b,some (if b then 11 else 9)⟩
  else if q = 8 then ⟨b,false,some 6⟩
  else if q = 9 then ⟨b,false,some 7⟩
  else if q = 10 then ⟨b,true,some 12⟩
  else if q = 11 then ⟨b,true,some 13⟩
  else shiftRow 12 (continuation (q-12) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 2 ≤ states) (hv : Closed states continuation) : Closed (12+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hsmall : q < 12
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have h0 : q ≠ 0 := by omega
    have h1 : q ≠ 1 := by omega
    have h2 : q ≠ 2 := by omega
    have h3 : q ≠ 3 := by omega
    have h4 : q ≠ 4 := by omega
    have h5 : q ≠ 5 := by omega
    have h6 : q ≠ 6 := by omega
    have h7 : q ≠ 7 := by omega
    have h8 : q ≠ 8 := by omega
    have h9 : q ≠ 9 := by omega
    have h10 : q ≠ 10 := by omega
    have h11 : q ≠ 11 := by omega
    have ht : (shiftRow 12 (continuation (q-12) b)).next = some q' := by
      simpa [table,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11] using hnext
    have hq0 : q-12 < states := by omega
    cases he : (continuation (q-12) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hv (q-12) hq0 b r he
      simp [shiftRow,he] at ht
      subst q'
      omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (12+q) b = shiftRow 12 (continuation q b) := by
  have h0 : 12+q ≠ 0 := by omega
  have h1 : 12+q ≠ 1 := by omega
  have h2 : 12+q ≠ 2 := by omega
  have h3 : 12+q ≠ 3 := by omega
  have h4 : 12+q ≠ 4 := by omega
  have h5 : 12+q ≠ 5 := by omega
  have h6 : 12+q ≠ 6 := by omega
  have h7 : 12+q ≠ 7 := by omega
  have h8 : 12+q ≠ 8 := by omega
  have h9 : 12+q ≠ 9 := by omega
  have h10 : 12+q ≠ 10 := by omega
  have h11 : 12+q ≠ 11 := by omega
  simp [table,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 12 c) = shiftConfig 12 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 12 c) fuel = shiftConfig 12 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem scratch_append (xs ys : List Bool) (tail : Nat) :
    scratch (xs++ys) tail = scratch xs (scratch ys tail) := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [scratch,ih]

theorem push_append (left : Nat) (xs ys : List Bool) :
    push left (xs++ys) = push (push left xs) ys := by
  induction xs generalizing left with
  | nil => rfl
  | cons b bs ih => simpa [push] using ih (4*left+2*bit b)

theorem startup (continuation : Nat → Bool → Row) (left stream : Nat) :
    step (table continuation) ⟨left,2*stream,some 0⟩ = ⟨2*stream+1,left,some 1⟩ := by
  simp [step,table,bit,Nat.testBit_zero]

theorem forward_marked (continuation : Nat → Bool → Row) (left tail : Nat) :
    run (table continuation) ⟨left,1+4*tail,some 1⟩ 2 = ⟨4*left+2,tail,some 1⟩ := by
  simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;>
    congr 1 <;> try split_ifs
  all_goals repeat' apply And.intro
  all_goals omega

theorem forward_prefix (continuation : Nat → Bool → Row) (k left tail : Nat) :
    run (table continuation) ⟨left,scratch (List.replicate k true) tail,some 1⟩ (2*k) =
      ⟨push left (List.replicate k true),tail,some 1⟩ := by
  induction k generalizing left with
  | zero => simp [scratch,push,run]
  | succ k ih =>
    have ht : 2*(k+1) = 2+2*k := by omega
    rw [ht,Source284PayloadPop.run_add]
    change run (table continuation)
      (run (table continuation) ⟨left,1+4*scratch (List.replicate k true) tail,some 1⟩ 2) _ = _
    rw [forward_marked,ih]
    simp [List.replicate_succ,push,bit]

theorem found_step1 (continuation : Nat → Bool → Row) (left tail : Nat) :
    step (table continuation) ⟨left,4*tail,some 1⟩ = ⟨2*left,2*tail,some 3⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega

theorem found_step2 (continuation : Nat → Bool → Row) (left tail : Nat) :
    step (table continuation) ⟨2*left,2*tail,some 3⟩ = ⟨2*tail,2*left,some 4⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega

theorem found_step3 (continuation : Nat → Bool → Row) (left tail : Nat) :
    step (table continuation) ⟨2*tail,2*left,some 4⟩ = ⟨4*tail+1,left,some 6⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega

theorem found (continuation : Nat → Bool → Row) (left tail : Nat) :
    run (table continuation) ⟨left,4*tail,some 1⟩ 3 = ⟨4*tail+1,left,some 6⟩ := by
  rw [Source284HardwireTable.run_front,found_step1,Source284HardwireTable.run_front,found_step2,
    Source284HardwireTable.run_front,found_step3]
  rfl

theorem exhausted_step1 (continuation : Nat → Bool → Row) (left certificate : Nat) :
    step (table continuation) ⟨left,4*certificate+2,some 1⟩ = ⟨2*left,2*certificate+1,some 3⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem exhausted_step2 (continuation : Nat → Bool → Row) (left certificate : Nat) :
    step (table continuation) ⟨2*left,2*certificate+1,some 3⟩ = ⟨2*certificate+1,2*left,some 5⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem exhausted_step3 (continuation : Nat → Bool → Row) (left certificate : Nat) :
    step (table continuation) ⟨2*certificate+1,2*left,some 5⟩ = ⟨4*certificate+2,left,some 7⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega

theorem exhausted (continuation : Nat → Bool → Row) (left certificate : Nat) :
    run (table continuation) ⟨left,4*certificate+2,some 1⟩ 3 =
      ⟨4*certificate+2,left,some 7⟩ := by
  rw [Source284HardwireTable.run_front,exhausted_step1,Source284HardwireTable.run_front,exhausted_step2,
    Source284HardwireTable.run_front,exhausted_step3]
  rfl

theorem back_pair (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (left right : Nat) :
    run (table continuation) ⟨left,4*right+2,some (6+mode)⟩ 2 =
      ⟨4*left+1,right,some (6+mode)⟩ := by
  interval_cases mode <;>
    simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> try split_ifs
  all_goals repeat' apply And.intro
  all_goals omega

theorem replicate_snoc (k : Nat) : List.replicate (k+1) true = List.replicate k true ++ [true] := by
  rw [List.replicate_add]
  simp

theorem back_prefix (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (k left boundary : Nat) :
    run (table continuation) ⟨left,push boundary (List.replicate k true),some (6+mode)⟩ (2*k) =
      ⟨scratch (List.replicate k true) left,boundary,some (6+mode)⟩ := by
  induction k generalizing left with
  | zero => simp [push,scratch,run]
  | succ k ih =>
    rw [replicate_snoc,push_append]
    have ht : 2*(k+1) = 2+2*k := by omega
    rw [ht,Source284PayloadPop.run_add]
    change run (table continuation)
      (run (table continuation) ⟨left,4*push boundary (List.replicate k true)+2,some (6+mode)⟩ 2) _ = _
    rw [back_pair _ _ hm,ih,Source284PayloadLoop.scratch_snoc]
    simp [bit]

theorem restore_boundary (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (left stream : Nat) :
    run (table continuation) ⟨left,2*stream+1,some (6+mode)⟩ 2 =
      ⟨left,2*stream,some (12+mode)⟩ := by
  interval_cases mode <;>
    simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> try split_ifs
  all_goals repeat' apply And.intro
  all_goals omega

/-- One unmarked pair is set to one. All other pair data, the certificate,
and the complete scratch half are restored. -/
theorem mark_first (continuation : Nat → Bool → Row) (k : Nat) (rest : List Bool)
    (certificate stream : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate k true ++ false::rest) certificate,2*stream,some 0⟩ (4*k+6) =
      ⟨pairTape (List.replicate k true ++ true::rest) certificate,2*stream,some 12⟩ := by
  have ht : 4*k+6 = 1+(2*k+(3+(2*k+2))) := by omega
  rw [ht,Source284PayloadPop.run_add _ _ 1 (2*k+(3+(2*k+2)))]
  change run (table continuation)
    (step (table continuation) ⟨pairTape (List.replicate k true ++ false::rest) certificate,2*stream,some 0⟩) _ = _
  rw [startup]
  unfold pairTape
  rw [scratch_append]
  rw [Source284PayloadPop.run_add _ _ (2*k) (3+(2*k+2)),forward_prefix]
  simp only [scratch,bit,Bool.false_eq_true,if_false,zero_add]
  change run (table continuation)
    ⟨push (2*stream+1) (List.replicate k true),4*scratch rest (4*certificate+2),some 1⟩ _ = _
  rw [Source284PayloadPop.run_add _ _ 3 (2*k+2),found]
  have he : 4*scratch rest (4*certificate+2)+1 = scratch (true::rest) (4*certificate+2) := by
    simp [scratch,bit] <;> omega
  rw [he]
  change run (table continuation) ⟨scratch (true::rest) (4*certificate+2),
    push (2*stream+1) (List.replicate k true),some (6+0)⟩ _ = _
  rw [Source284PayloadPop.run_add _ _ (2*k) 2,back_prefix _ _ (by decide),restore_boundary _ _ (by decide),
    ← scratch_append]

/-- If every pair is marked, the sentinel is detected and all data are
restored; the second continuation state reports exhaustion. -/
theorem all_marked (continuation : Nat → Bool → Row) (k certificate stream : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate k true) certificate,2*stream,some 0⟩ (4*k+6) =
      ⟨pairTape (List.replicate k true) certificate,2*stream,some 13⟩ := by
  have ht : 4*k+6 = 1+(2*k+(3+(2*k+2))) := by omega
  rw [ht,Source284PayloadPop.run_add _ _ 1 (2*k+(3+(2*k+2)))]
  change run (table continuation)
    (step (table continuation) ⟨pairTape (List.replicate k true) certificate,2*stream,some 0⟩) _ = _
  rw [startup]
  unfold pairTape
  rw [Source284PayloadPop.run_add _ _ (2*k) (3+(2*k+2)),forward_prefix]
  rw [Source284PayloadPop.run_add _ _ 3 (2*k+2),exhausted]
  change run (table continuation) ⟨4*certificate+2,
    push (2*stream+1) (List.replicate k true),some (6+1)⟩ _ = _
  rw [Source284PayloadPop.run_add _ _ (2*k) 2,back_prefix _ _ (by decide),restore_boundary _ _ (by decide)]

end Shared.Beeping.NPcoNP.Source284UnaryMarkOne
