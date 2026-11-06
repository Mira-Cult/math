import Shared.Beeping.NPcoNP.Source284PayloadMarkOne

/-! Reset a marked payload prefix while preserving payload bits, the false
sentinel, the complete high suffix and the certificate. The input invariant
is zero-marked prefix followed by one-marked suffix and its sentinel. -/
namespace Shared.Beeping.NPcoNP.Source284PayloadReset

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (push flipped)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add push_append)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)

/-- Before the first one marker, zero markers are restored to one. Once a
one is encountered, the remaining one markers are preserved until `00`.
The reference return pass restores the original head and certificate. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else if q = 2 then ⟨true,false,some (if b then 3 else 1)⟩
  else if q = 3 then ⟨b,false,some 4⟩
  else if q = 4 then ⟨b,false,some (if b then 3 else 5)⟩
  else shiftRow 5 (Source284ScratchFlipReturn.table continuation (q-5) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (11+states) (table continuation) := by
  have hc := Source284ScratchFlipReturn.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases hsmall : q < 5
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have h0 : q ≠ 0 := by omega
    have h1 : q ≠ 1 := by omega
    have h2 : q ≠ 2 := by omega
    have h3 : q ≠ 3 := by omega
    have h4 : q ≠ 4 := by omega
    have ht : (shiftRow 5 (Source284ScratchFlipReturn.table continuation (q-5) b)).next = some q' := by
      simpa [table,h0,h1,h2,h3,h4] using hnext
    have hq0 : q-5 < 6+states := by omega
    cases he : (Source284ScratchFlipReturn.table continuation (q-5) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hc (q-5) hq0 b r he
      simp [shiftRow,he] at ht
      subst q'
      omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (5+q) b = shiftRow 5 (Source284ScratchFlipReturn.table continuation q b) := by
  have h0 : 5+q ≠ 0 := by omega
  have h1 : 5+q ≠ 1 := by omega
  have h2 : 5+q ≠ 2 := by omega
  have h3 : 5+q ≠ 3 := by omega
  have h4 : 5+q ≠ 4 := by omega
  simp [table,h0,h1,h2,h3,h4]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 5 c) =
      shiftConfig 5 (step (Source284ScratchFlipReturn.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 5 c) fuel =
      shiftConfig 5 (run (Source284ScratchFlipReturn.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem startup (continuation : Nat → Bool → Row) (left stream : Nat) :
    step (table continuation) ⟨left,2*stream,some 0⟩ = ⟨2*left,stream,some 1⟩ := by
  simp [step,table,bit,Nat.testBit_zero]

theorem zero_pair (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    run (table continuation) ⟨left,bit b+4*tail,some 1⟩ 2 =
      ⟨4*left+2*bit b+1,tail,some 1⟩ := by
  cases b <;> simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> try split_ifs
  all_goals repeat' constructor
  all_goals omega

theorem zero_prefix (continuation : Nat → Bool → Row) (xs : List Bool) (left tail : Nat) :
    run (table continuation) ⟨left,zeros xs tail,some 1⟩ (2*xs.length) =
      ⟨push left xs,tail,some 1⟩ := by
  induction xs generalizing left with
  | nil => simp [zeros,push,run]
  | cons b bs ih =>
    have ht : 2*(b::bs).length = 2+2*bs.length := by simp; omega
    rw [ht,run_add]
    simp only [zeros,push]
    rw [zero_pair,ih]

theorem first_one (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    run (table continuation) ⟨left,bit b+2+4*tail,some 1⟩ 2 =
      ⟨4*left+2*bit b+1,tail,some 3⟩ := by
  cases b <;> simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> try split_ifs
  all_goals repeat' constructor
  all_goals omega

theorem one_pair (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    run (table continuation) ⟨left,bit b+2+4*tail,some 3⟩ 2 =
      ⟨4*left+2*bit b+1,tail,some 3⟩ := by
  cases b <;> simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> try split_ifs
  all_goals repeat' constructor
  all_goals omega

theorem one_suffix (continuation : Nat → Bool → Row) (ys : List Bool) (left tail : Nat) :
    run (table continuation) ⟨left,flipped ys tail,some 3⟩ (2*ys.length) =
      ⟨push left ys,4*tail,some 3⟩ := by
  induction ys generalizing left with
  | nil => simp [flipped,push,run]
  | cons b bs ih =>
    have ht : 2*(b::bs).length = 2+2*bs.length := by simp; omega
    rw [ht,run_add]
    simp only [flipped,push]
    rw [one_pair,ih]

theorem turn (continuation : Nat → Bool → Row) (left tail : Nat) :
    run (table continuation) ⟨left,4*tail,some 3⟩ 2 =
      shiftConfig 5 ⟨4*left,tail,some 0⟩ := by
  simp [run,step,table,shiftConfig,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod]
  try split_ifs
  all_goals repeat' constructor
  all_goals omega

/-- A nonempty unmarked suffix includes the sentinel. The pass resets the
entire prefix and restores all tape content except those marker bits. -/
theorem reset (continuation : Nat → Bool → Row) (xs ys : List Bool) (b : Bool)
    (certificate tail : Nat) :
    run (table continuation) ⟨certificate,2*zeros xs (flipped (b::ys) tail),some 0⟩
      (4*(xs.length+(b::ys).length)+8) =
      ⟨certificate,2*flipped (xs++b::ys) tail,some 11⟩ := by
  have ht : 4*(xs.length+(b::ys).length)+8 =
      1+(2*xs.length+(2+(2*ys.length+(2+(2*(xs++b::ys).length+5))))) := by simp; omega
  rw [ht,run_add _ _ 1 (2*xs.length+(2+(2*ys.length+(2+(2*(xs++b::ys).length+5)))))]
  change run (table continuation)
    (step (table continuation) ⟨certificate,2*zeros xs (flipped (b::ys) tail),some 0⟩) _ = _
  rw [startup,run_add _ _ (2*xs.length) (2+(2*ys.length+(2+(2*(xs++b::ys).length+5)))),zero_prefix]
  change run (table continuation)
    ⟨push (2*certificate) xs,bit b+2+4*flipped ys tail,some 1⟩ _ = _
  rw [run_add _ _ 2 (2*ys.length+(2+(2*(xs++b::ys).length+5))),first_one]
  rw [run_add _ _ (2*ys.length) (2+(2*(xs++b::ys).length+5)),one_suffix]
  have hp : push (4*push (2*certificate) xs+2*bit b+1) ys = push (2*certificate) (xs++b::ys) := by
    rw [push_append]
    rfl
  rw [hp,run_add _ _ 2 (2*(xs++b::ys).length+5),turn,relocated_run,
    Source284ScratchFlipReturn.return_frame]
  rfl

/-- Specialized form where the unmarked suffix ends in the explicit false
sentinel; the list `rest` may be empty. -/
theorem reset_sentinel (continuation : Nat → Bool → Row) (xs rest : List Bool)
    (certificate tail : Nat) :
    run (table continuation) ⟨certificate,2*zeros xs (flipped (rest++[false]) tail),some 0⟩
      (4*(xs.length+rest.length)+12) =
      ⟨certificate,2*flipped ((xs++rest)++[false]) tail,some 11⟩ := by
  cases rest with
  | nil =>
    have h := reset continuation xs [] false certificate tail
    simp only [List.length_cons,List.length_nil] at h
    have ht : 4*(xs.length+1)+8 = 4*(xs.length+0)+12 := by omega
    rw [ht] at h
    simpa using h
  | cons b ys =>
    have h := reset continuation xs (ys++[false]) b certificate tail
    simp only [List.length_cons,List.length_append,List.length_nil,List.length_singleton] at h
    have ht : 4*(xs.length+(ys.length+1+1))+8 = 4*(xs.length+(ys.length+1))+12 := by omega
    rw [ht] at h
    simpa [List.append_assoc] using h

end Shared.Beeping.NPcoNP.Source284PayloadReset
