import Shared.Beeping.NPcoNP.Source284WitnessScannerRun

/-! A finite relative-table transducer for a two-sided witness frame.
Two zero bits below the frame mark the return boundary. States are logical
source states, not physical 284-machine states. This module neither enforces
a witness cutoff nor constructs a verifier input or proves bit complexity. -/
namespace Shared.Beeping.NPcoNP.Source284TaggedWitnessRoundtrip

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284WitnessScanner (bit_decide_mod lowbit_value)
open Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic (pushPairs)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

def table : Nat → Bool → Row
 | 0, b => ⟨b, true, some 1⟩
 | 1, b => ⟨b, false, some 2⟩
 | 2, b => ⟨b, false, some 3⟩
 | 3, b => ⟨b, false, some (if b then 4 else 5)⟩
 | 4, b => ⟨b, false, some 3⟩
 | 5, b => ⟨b, true, some 6⟩
 | 6, b => ⟨b, false, some 7⟩
 | 7, b => ⟨b, false, some 8⟩
 | 8, b => ⟨b, false, some (if b then 7 else 9)⟩
 | _, b => ⟨b, false, some 9⟩

theorem table_closed : Closed 10 table := by
  intro q hq b q' hn
  interval_cases q <;> cases b <;> simp_all [table] <;> omega

theorem record_count : (records 10 table).length = 20 := by
  simp [records]

theorem run_add (c : Config) (a b : Nat) :
    run table c (a+b) = run table (run table c a) b := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    change step table (run table c (a+b)) = step table (run table (run table c a) b)
    rw [ih]

theorem turn (q q' left right : Nat)
    (h : ∀ b, table q b = ⟨b, true, some q'⟩) :
    step table ⟨left,right,some q⟩ = ⟨right,left,some q'⟩ := by
  simp only [step, h, ↓reduceIte]
  rw [lowbit_value]
  congr 1 <;> omega

theorem straight (q q' left right : Nat)
    (h : ∀ b, table q b = ⟨b, false, some q'⟩) :
    step table ⟨left,right,some q⟩ = ⟨2*left+right%2,right/2,some q'⟩ := by
  simp [step, h, Nat.testBit_zero, bit_decide_mod]

theorem marker (q left right : Nat) (hq : q = 3 ∨ q = 8) :
    step table ⟨left,right,some q⟩ =
      ⟨2*left+right%2,right/2,
        some (if right.testBit 0 then (if q=3 then 4 else 7) else (if q=3 then 5 else 9))⟩ := by
  rcases hq with rfl | rfl <;>
    simp [step, table, Nat.testBit_zero, bit_decide_mod]

/-- Exactly two source steps consume one forward marker/payload pair. -/
theorem forward_pair (left suffix : Nat) (b : Bool) (rest : List Bool) :
    run table ⟨left,encodeFrame (b::rest) suffix,some 3⟩ 2 =
      ⟨4*left+2+(if b then 1 else 0),encodeFrame rest suffix,some 3⟩ := by
  cases b <;> simp [run, marker, straight, table, encodeFrame, Nat.testBit_zero,
    Nat.add_mod, Nat.mul_mod] <;> congr 1 <;> omega

/-- A finite witness frame reaches the reverse-turn boundary. -/
theorem forward_frame (w : List Bool) (left suffix : Nat) :
    run table ⟨left,encodeFrame w suffix,some 3⟩ (2*w.length+1) =
      ⟨2*pushPairs left w,suffix,some 5⟩ := by
  induction w generalizing left with
  | nil => simp [run, marker, encodeFrame, pushPairs, Nat.testBit_zero]
  | cons b bs ih =>
    have ht : 2*(b::bs).length+1 = 2 + (2*bs.length+1) := by simp; omega
    rw [ht, run_add, forward_pair]
    simpa [pushPairs] using ih (4*left+2+(if b then 1 else 0))

/-- Encoded source-table run, valid for every high tail on the table code. -/
theorem source_run (c : Config) (valid : Valid 10 c) (tail steps : Nat) :
    Shared.Beeping.NPcoNP.Source284Relative.run (encode 10 table tail) (toSource c) steps =
      toSource (run table c steps) :=
  run_toSource 10 table tail c table_closed valid steps

end Shared.Beeping.NPcoNP.Source284TaggedWitnessRoundtrip
namespace Shared.Beeping.NPcoNP.Source284TaggedWitnessRoundtrip
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic (pushPairs)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

theorem pushPairs_append (input : Nat) (xs ys : List Bool) :
  pushPairs input (xs ++ ys) = pushPairs (pushPairs input xs) ys := by
  induction xs generalizing input with
  | nil => rfl
  | cons b bs ih => simpa [pushPairs] using ih (4 * input + 2 + (if b then 1 else 0))

theorem pushPairs_snoc (input : Nat) (xs : List Bool) (b : Bool) :
  pushPairs input (xs ++ [b]) = 4 * pushPairs input xs + 2 + (if b then 1 else 0) := by
  rw [pushPairs_append]
  rfl

def rawPairs : List Bool → Nat → Nat
 | [], tail => tail
 | b::bs, tail => 4 * rawPairs bs tail + 2 * (if b then 1 else 0) + 1

theorem rawPairs_append (xs ys : List Bool) (tail : Nat) :
    rawPairs (xs ++ ys) tail = rawPairs xs (rawPairs ys tail) := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [rawPairs, ih]

theorem rawPairs_frame (xs : List Bool) (suffix : Nat) :
    rawPairs xs (2*suffix) = encodeFrame xs suffix := by
  induction xs with
  | nil => simp [rawPairs, encodeFrame]
  | cons b bs ih =>
    simp only [rawPairs, encodeFrame]
    rw [ih]
    cases b <;> simp <;> omega

theorem reverse_pair (left right : Nat) (b : Bool) :
    run table ⟨left,4*right+2+(if b then 1 else 0),some 7⟩ 2 =
      ⟨4*left+2*(if b then 1 else 0)+1,right,some 7⟩ := by
  cases b <;> simp [run, straight, marker, table, Nat.testBit_zero,
    Nat.add_mod, Nat.mul_mod] <;> congr 1 <;> omega

theorem reverse_pairs (w : List Bool) (left right : Nat) :
    run table ⟨left,pushPairs right w,some 7⟩ (2*w.length) =
      ⟨rawPairs w left,right,some 7⟩ := by
  induction w using List.reverseRecOn generalizing left with
  | nil => simp [run, pushPairs, rawPairs]
  | append_singleton w b ih =>
    rw [pushPairs_snoc]
    have ht : 2*(w ++ [b]).length = 2 + 2*w.length := by simp; omega
    rw [ht, run_add, reverse_pair, ih]
    rw [rawPairs_append]
    rfl
end Shared.Beeping.NPcoNP.Source284TaggedWitnessRoundtrip
namespace Shared.Beeping.NPcoNP.Source284TaggedWitnessRoundtrip
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic (pushPairs)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

theorem tag_begin (input cert : Nat) :
  run table ⟨4*cert,input,some 0⟩ 3 = ⟨4*input,cert,some 3⟩ := by
  simp [run, turn, straight, table] <;> congr 1 <;> omega

theorem tag_middle (left suffix : Nat) :
  run table ⟨2*left,suffix,some 5⟩ 2 = ⟨2*suffix,left,some 7⟩ := by
  simp [run, turn, straight, table] <;> congr 1 <;> omega

theorem tag_finish (left input : Nat) :
  run table ⟨left,4*input,some 7⟩ 2 = ⟨4*left,input,some 9⟩ := by
  simp [run, straight, marker, table, Nat.testBit_zero, Nat.add_mod, Nat.mul_mod] <;>
    congr 1 <;> omega

theorem tagged_roundtrip (w : List Bool) (input suffix : Nat) :
  run table ⟨4*encodeFrame w suffix,input,some 0⟩ (4*w.length+8) =
    ⟨4*encodeFrame w suffix,input,some 9⟩ := by
  have ht : 4*w.length+8 = 3 + (2*w.length+1) + 2 + 2*w.length + 2 := by omega
  rw [ht, run_add, run_add, run_add, run_add, tag_begin, forward_frame, tag_middle,
    reverse_pairs, rawPairs_frame, tag_finish]
/-- At the stated time, both numeric tape halves are restored and control is
in state 9, which continues executing. The tags are an explicit input
precondition; this is not yet a cutoff wrapper. -/
theorem source_tagged_roundtrip (w : List Bool) (input suffix tail : Nat) :
    Shared.Beeping.NPcoNP.Source284Relative.run
      (Shared.Beeping.NPcoNP.Source284TableEncode.encode 10 table tail)
      (Shared.Beeping.NPcoNP.Source284Relative.initial input (4*encodeFrame w suffix))
      (4*w.length+8) = ⟨4*encodeFrame w suffix,input,19⟩ := by
  have hv : Valid 10 ⟨4*encodeFrame w suffix,input,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    omega
  have h := source_run ⟨4*encodeFrame w suffix,input,some 0⟩ hv tail (4*w.length+8)
  change Shared.Beeping.NPcoNP.Source284Relative.run
    (Shared.Beeping.NPcoNP.Source284TableEncode.encode 10 table tail)
    (Shared.Beeping.NPcoNP.Source284Relative.initial input (4*encodeFrame w suffix)) _ = _ at h
  rw [h, tagged_roundtrip]
  rfl

end Shared.Beeping.NPcoNP.Source284TaggedWitnessRoundtrip
