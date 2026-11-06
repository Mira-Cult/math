import Shared.Beeping.NPcoNP.Source284PayloadSentinelPipeline

/-! A finite transition table marks the next payload pair or detects the
sentinel. Pair markers on already processed payload are zero; unprocessed
markers are one. The sentinel is one extra false/one pair followed by a
zero/zero terminator. No runtime data depend on a semantic oracle. -/
namespace Shared.Beeping.NPcoNP.Source284PayloadMarkOne

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

/-- Processed pairs have a zero marker and preserve their data bits. -/
def zeros : List Bool → Nat → Nat
  | [], tail => tail
  | b::bs, tail => bit b+4*zeros bs tail

/-- Stack left behind by a forward scan of processed pairs. -/
def push : Nat → List Bool → Nat
  | left, [] => left
  | left, b::bs => push (4*left+2*bit b) bs

theorem zeros_append (xs ys : List Bool) (tail : Nat) :
    zeros (xs++ys) tail = zeros xs (zeros ys tail) := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [zeros,ih]

theorem push_append (left : Nat) (xs ys : List Bool) :
    push left (xs++ys) = push (push left xs) ys := by
  induction xs generalizing left with
  | nil => rfl
  | cons b bs ih => simpa [push] using ih (4*left+2*bit b)

theorem push_snoc (left : Nat) (xs : List Bool) (b : Bool) :
    push left (xs++[b]) = 4*push left xs+2*bit b := by
  rw [push_append]
  rfl

/-- Two continuation entries distinguish success and exhaustion. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨true,false,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else if q = 2 then ⟨b,false,some (if b then 3 else 1)⟩
  else if q = 3 then ⟨b,false,some 4⟩
  else if q = 4 then ⟨b,true,some (if b then 5 else 10)⟩
  else if q = 5 then ⟨b,false,some 6⟩
  else if q = 6 then ⟨false,false,some 7⟩
  else if q = 7 then ⟨b,false,some 8⟩
  else if q = 8 then ⟨false,false,some (if b then 14 else 7)⟩
  else if q = 9 then ⟨b,false,some 9⟩
  else if q = 10 then ⟨b,false,some 11⟩
  else if q = 11 then ⟨b,false,some 12⟩
  else if q = 12 then ⟨b,false,some 13⟩
  else if q = 13 then ⟨false,false,some (if b then 15 else 12)⟩
  else if q = 14 then ⟨b,true,some 17⟩
  else if q = 15 then ⟨b,true,some 18⟩
  else if q = 16 then ⟨b,false,some 16⟩
  else shiftRow 17 (continuation (q-17) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 2 ≤ states) (hv : Closed states continuation) : Closed (17+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hsmall : q < 17
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
    have h12 : q ≠ 12 := by omega
    have h13 : q ≠ 13 := by omega
    have h14 : q ≠ 14 := by omega
    have h15 : q ≠ 15 := by omega
    have h16 : q ≠ 16 := by omega
    have ht : (shiftRow 17 (continuation (q-17) b)).next = some q' := by
      simpa [table,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16] using hnext
    have hq0 : q-17 < states := by omega
    cases he : (continuation (q-17) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hv (q-17) hq0 b r he
      simp [shiftRow,he] at ht
      subst q'
      omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (17+q) b = shiftRow 17 (continuation q b) := by
  have hn : ∀ k < 17, 17+q ≠ k := by intros; omega
  simp [table,hn 0 (by omega),hn 1 (by omega),hn 2 (by omega),hn 3 (by omega),
    hn 4 (by omega),hn 5 (by omega),hn 6 (by omega),hn 7 (by omega),hn 8 (by omega),
    hn 9 (by omega),hn 10 (by omega),hn 11 (by omega),hn 12 (by omega),hn 13 (by omega),
    hn 14 (by omega),hn 15 (by omega),hn 16 (by omega)]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 17 c) = shiftConfig 17 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table continuation) (shiftConfig 17 c) clock = shiftConfig 17 (run continuation c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

theorem startup (continuation : Nat → Bool → Row) (certificate stream : Nat) :
    step (table continuation) ⟨certificate,2*stream,some 0⟩ =
      ⟨2*certificate+1,stream,some 1⟩ := by
  simp [step,table,bit,Nat.testBit_zero]

theorem forward_pair (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    run (table continuation) ⟨left,bit b+4*tail,some 1⟩ 2 =
      ⟨4*left+2*bit b,tail,some 1⟩ := by
  cases b <;> simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;>
    try split_ifs
  all_goals repeat' apply And.intro
  all_goals omega

theorem forward_prefix (continuation : Nat → Bool → Row) (xs : List Bool) (left tail : Nat) :
    run (table continuation) ⟨left,zeros xs tail,some 1⟩ (2*xs.length) =
      ⟨push left xs,tail,some 1⟩ := by
  induction xs generalizing left with
  | nil => simp [zeros,push,run]
  | cons b bs ih =>
    have ht : 2*(b::bs).length = 2+2*bs.length := by simp; omega
    rw [ht,run_add]
    simp only [zeros,push]
    rw [forward_pair,ih]

/-- The next marked pair has another marked pair after it, so it is real
payload. The pass clears only its marker and turns toward the boundary. -/
theorem found (continuation : Nat → Bool → Row) (left tail : Nat) (b c : Bool) :
    run (table continuation) ⟨left,bit b+2+4*(bit c+2+4*tail),some 1⟩ 7 =
      ⟨bit b+4*(bit c+2+4*tail),left,some 8⟩ := by
  have h1 : step (table continuation) ⟨left,bit b+2+4*(bit c+2+4*tail),some 1⟩ =
      ⟨2*left+bit b,1+2*(bit c+2+4*tail),some 2⟩ := by
    cases b <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
    all_goals repeat' constructor
    all_goals omega
  have h2 : step (table continuation) ⟨2*left+bit b,1+2*(bit c+2+4*tail),some 2⟩ =
      ⟨4*left+2*bit b+1,bit c+2+4*tail,some 3⟩ := by
    cases b <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
    all_goals repeat' constructor
    all_goals omega
  have h3 : step (table continuation) ⟨4*left+2*bit b+1,bit c+2+4*tail,some 3⟩ =
      ⟨2*(4*left+2*bit b+1)+bit c,1+2*tail,some 4⟩ := by
    cases c <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
    all_goals repeat' constructor
    all_goals omega
  have h4 : step (table continuation) ⟨2*(4*left+2*bit b+1)+bit c,1+2*tail,some 4⟩ =
      ⟨2*tail+1,2*(4*left+2*bit b+1)+bit c,some 5⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
    omega
  have h5 : step (table continuation) ⟨2*tail+1,2*(4*left+2*bit b+1)+bit c,some 5⟩ =
      ⟨4*tail+2+bit c,4*left+2*bit b+1,some 6⟩ := by
    cases c <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
    all_goals repeat' constructor
    all_goals omega
  have h6 : step (table continuation) ⟨4*tail+2+bit c,4*left+2*bit b+1,some 6⟩ =
      ⟨2*(4*tail+2+bit c),2*left+bit b,some 7⟩ := by
    cases b <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
    all_goals repeat' constructor
    all_goals omega
  have h7 : step (table continuation) ⟨2*(4*tail+2+bit c),2*left+bit b,some 7⟩ =
      ⟨bit b+4*(bit c+2+4*tail),left,some 8⟩ := by
    cases b <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
    all_goals repeat' constructor
    all_goals omega
  rw [run_front,h1,run_front,h2,run_front,h3,run_front,h4,run_front,h5,
    run_front,h6,run_front,h7]
  rfl

/-- The extra false/one pair followed by zero/zero is the sentinel; it is
left unchanged even when the suffix above it is arbitrary. -/
theorem exhausted (continuation : Nat → Bool → Row) (left tail : Nat) :
    run (table continuation) ⟨left,2+16*tail,some 1⟩ 7 =
      ⟨2+16*tail,left,some 13⟩ := by
  have h1 : step (table continuation) ⟨left,2+16*tail,some 1⟩ =
      ⟨2*left,1+8*tail,some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
    all_goals repeat' constructor
    all_goals omega
  have h2 : step (table continuation) ⟨2*left,1+8*tail,some 2⟩ =
      ⟨4*left+1,4*tail,some 3⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
    all_goals repeat' constructor
    all_goals omega
  have h3 : step (table continuation) ⟨4*left+1,4*tail,some 3⟩ =
      ⟨8*left+2,2*tail,some 4⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
    all_goals repeat' constructor
    all_goals omega
  have h4 : step (table continuation) ⟨8*left+2,2*tail,some 4⟩ =
      ⟨2*tail,8*left+2,some 10⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
  have h5 : step (table continuation) ⟨2*tail,8*left+2,some 10⟩ =
      ⟨4*tail,4*left+1,some 11⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
    all_goals repeat' constructor
    all_goals omega
  have h6 : step (table continuation) ⟨4*tail,4*left+1,some 11⟩ =
      ⟨8*tail+1,2*left,some 12⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
    all_goals repeat' constructor
    all_goals omega
  have h7 : step (table continuation) ⟨8*tail+1,2*left,some 12⟩ =
      ⟨2+16*tail,left,some 13⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
    all_goals repeat' constructor
    all_goals omega
  rw [run_front,h1,run_front,h2,run_front,h3,run_front,h4,run_front,h5,
    run_front,h6,run_front,h7]
  rfl

theorem back_pair (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (left right : Nat) (b : Bool) :
    run (table continuation) ⟨left,4*right+2*bit b,some (8+5*mode)⟩ 2 =
      ⟨bit b+4*left,right,some (8+5*mode)⟩ := by
  interval_cases mode <;> cases b <;>
    simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> try split_ifs
  all_goals repeat' apply And.intro
  all_goals omega

theorem back_prefix (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (xs : List Bool) (left boundary : Nat) :
    run (table continuation) ⟨left,push boundary xs,some (8+5*mode)⟩ (2*xs.length) =
      ⟨zeros xs left,boundary,some (8+5*mode)⟩ := by
  induction xs using List.reverseRecOn generalizing left with
  | nil => simp [push,zeros,run]
  | append_singleton xs b ih =>
    rw [push_snoc]
    have ht : 2*(xs++[b]).length = 2+2*xs.length := by simp; omega
    rw [ht,run_add,back_pair _ _ hm,ih,zeros_append]
    simp [zeros]

theorem restore_boundary (continuation : Nat → Bool → Row) (mode : Nat) (hm : mode < 2)
    (stream certificate : Nat) :
    run (table continuation) ⟨stream,2*certificate+1,some (8+5*mode)⟩ 2 =
      ⟨certificate,2*stream,some (17+mode)⟩ := by
  interval_cases mode <;>
    simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> try split_ifs
  all_goals repeat' apply And.intro
  all_goals omega

/-- Mark exactly the first unprocessed pair. The required following pair can
be either another payload pair or the sentinel. -/
theorem mark_next (continuation : Nat → Bool → Row) (xs ys : List Bool)
    (b c : Bool) (certificate tail : Nat) :
    run (table continuation)
      ⟨certificate,2*zeros xs (flipped (b::c::ys) tail),some 0⟩ (4*xs.length+10) =
      ⟨certificate,2*zeros (xs++[b]) (flipped (c::ys) tail),some 17⟩ := by
  have ht : 4*xs.length+10 = 1+(2*xs.length+(7+(2*xs.length+2))) := by omega
  rw [ht,run_add _ _ 1 (2*xs.length+(7+(2*xs.length+2)))]
  change run (table continuation)
    (step (table continuation) ⟨certificate,2*zeros xs (flipped (b::c::ys) tail),some 0⟩) _ = _
  rw [startup,run_add _ _ (2*xs.length) (7+(2*xs.length+2)),forward_prefix]
  change run (table continuation) ⟨push (2*certificate+1) xs,
    bit b+2+4*(bit c+2+4*flipped ys tail),some 1⟩ _ = _
  rw [run_add _ _ 7 (2*xs.length+2),found]
  change run (table continuation) ⟨bit b+4*(bit c+2+4*flipped ys tail),
    push (2*certificate+1) xs,some (8+5*0)⟩ _ = _
  rw [run_add _ _ (2*xs.length) 2,back_prefix _ _ (by decide),restore_boundary _ _ (by decide)]
  simp [zeros_append,zeros,flipped]

/-- Once all real payload pairs are marked, the false sentinel is detected
and the entire tape is restored. -/
theorem all_marked (continuation : Nat → Bool → Row) (xs : List Bool) (certificate tail : Nat) :
    run (table continuation) ⟨certificate,2*zeros xs (flipped [false] tail),some 0⟩
      (4*xs.length+10) =
      ⟨certificate,2*zeros xs (flipped [false] tail),some 18⟩ := by
  have ht : 4*xs.length+10 = 1+(2*xs.length+(7+(2*xs.length+2))) := by omega
  rw [ht,run_add _ _ 1 (2*xs.length+(7+(2*xs.length+2)))]
  change run (table continuation)
    (step (table continuation) ⟨certificate,2*zeros xs (flipped [false] tail),some 0⟩) _ = _
  rw [startup,run_add _ _ (2*xs.length) (7+(2*xs.length+2)),forward_prefix]
  have he : flipped [false] tail = 2+16*tail := by simp [flipped,bit]; omega
  rw [he]
  rw [run_add _ _ 7 (2*xs.length+2),exhausted]
  change run (table continuation) ⟨2+16*tail,
    push (2*certificate+1) xs,some (8+5*1)⟩ _ = _
  rw [run_add _ _ (2*xs.length) 2,back_prefix _ _ (by decide),restore_boundary _ _ (by decide)]

end Shared.Beeping.NPcoNP.Source284PayloadMarkOne
