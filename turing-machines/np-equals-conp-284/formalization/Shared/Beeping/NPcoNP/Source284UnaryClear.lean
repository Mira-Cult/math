import Shared.Beeping.NPcoNP.Source284UnaryMarkOneSource

/-! A finite source table clears arbitrary marks in a prepared unary-pair
region, restores the scratch boundary, and preserves the complete certificate.
This is a reusable reset operation, not yet a payload-length comparator. -/
namespace Shared.Beeping.NPcoNP.Source284UnaryClear

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284PayloadLoop (scratch)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchSentinel (unaryPairs)

/-- Turn toward the token pairs, clear each data cell, stop at the `0,1`
sentinel, then return to the temporarily marked scratch boundary. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨true,true,some 1⟩
  else if q = 1 then ⟨false,false,some 2⟩
  else if q = 2 then ⟨b,b,some (if b then 3 else 1)⟩
  else if q = 3 then ⟨b,false,some 4⟩
  else if q = 4 then ⟨false,b,some (if b then 6 else 5)⟩
  else if q = 5 then ⟨b,false,some 4⟩
  else if q = 6 then ⟨b,true,some 7⟩
  else shiftRow 7 (continuation (q-7) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (7+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hsmall : q < 7
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have h0 : q ≠ 0 := by omega
    have h1 : q ≠ 1 := by omega
    have h2 : q ≠ 2 := by omega
    have h3 : q ≠ 3 := by omega
    have h4 : q ≠ 4 := by omega
    have h5 : q ≠ 5 := by omega
    have h6 : q ≠ 6 := by omega
    have ht : (shiftRow 7 (continuation (q-7) b)).next = some q' := by
      simpa [table,h0,h1,h2,h3,h4,h5,h6] using hnext
    have hq0 : q-7 < states := by omega
    cases he : (continuation (q-7) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hv (q-7) hq0 b r he
      simp [shiftRow,he] at ht
      subst q'
      omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (7+q) b = shiftRow 7 (continuation q b) := by
  have h0 : 7+q ≠ 0 := by omega
  have h1 : 7+q ≠ 1 := by omega
  have h2 : 7+q ≠ 2 := by omega
  have h3 : 7+q ≠ 3 := by omega
  have h4 : 7+q ≠ 4 := by omega
  have h5 : 7+q ≠ 5 := by omega
  have h6 : 7+q ≠ 6 := by omega
  simp [table,h0,h1,h2,h3,h4,h5,h6]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 7 c) = shiftConfig 7 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 7 c) fuel = shiftConfig 7 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem startup (continuation : Nat → Bool → Row) (left stream : Nat) :
    step (table continuation) ⟨left,2*stream,some 0⟩ = ⟨2*stream+1,left,some 1⟩ := by
  simp [step,table,bit,Nat.testBit_zero]

theorem clear_pair_step1 (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    step (table continuation) ⟨left,bit b+4*tail,some 1⟩ = ⟨2*left,2*tail,some 2⟩ := by
  cases b <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem clear_pair_step2 (continuation : Nat → Bool → Row) (left tail : Nat) :
    step (table continuation) ⟨2*left,2*tail,some 2⟩ = ⟨4*left,tail,some 1⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega

theorem clear_pair (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    run (table continuation) ⟨left,bit b+4*tail,some 1⟩ 2 = ⟨4*left,tail,some 1⟩ := by
  rw [Source284HardwireTable.run_front,clear_pair_step1,Source284HardwireTable.run_front,clear_pair_step2]
  rfl

theorem clear_pairs (continuation : Nat → Bool → Row) (xs : List Bool) (left tail : Nat) :
    run (table continuation) ⟨left,scratch xs tail,some 1⟩ (2*xs.length) =
      ⟨4^xs.length*left,tail,some 1⟩ := by
  induction xs generalizing left with
  | nil => simp [scratch,run]
  | cons b bs ih =>
    have ht : 2*(b::bs).length = 2+2*bs.length := by simp; omega
    rw [ht,Source284PayloadPop.run_add]
    change run (table continuation)
      (run (table continuation) ⟨left,bit b+4*scratch bs tail,some 1⟩ 2) _ = _
    rw [clear_pair,ih]
    simp [pow_succ]
    ring

theorem sentinel_step1 (continuation : Nat → Bool → Row) (left certificate : Nat) :
    step (table continuation) ⟨left,4*certificate+2,some 1⟩ = ⟨2*left,2*certificate+1,some 2⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem sentinel_step2 (continuation : Nat → Bool → Row) (left certificate : Nat) :
    step (table continuation) ⟨2*left,2*certificate+1,some 2⟩ = ⟨2*certificate+1,2*left,some 3⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega

theorem sentinel_step3 (continuation : Nat → Bool → Row) (left certificate : Nat) :
    step (table continuation) ⟨2*certificate+1,2*left,some 3⟩ = ⟨4*certificate+2,left,some 4⟩ := by
  simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega

theorem sentinel (continuation : Nat → Bool → Row) (left certificate : Nat) :
    run (table continuation) ⟨left,4*certificate+2,some 1⟩ 3 =
      ⟨4*certificate+2,left,some 4⟩ := by
  rw [Source284HardwireTable.run_front,sentinel_step1,Source284HardwireTable.run_front,sentinel_step2,
    Source284HardwireTable.run_front,sentinel_step3]
  rfl

theorem back_pair (continuation : Nat → Bool → Row) (left right : Nat) :
    run (table continuation) ⟨left,4*right,some 4⟩ 2 = ⟨4*left,right,some 4⟩ := by
  simp [run,step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> try split_ifs
  all_goals repeat' apply And.intro
  all_goals omega

theorem back_pairs (continuation : Nat → Bool → Row) (k left boundary : Nat) :
    run (table continuation) ⟨left,4^k*boundary,some 4⟩ (2*k) =
      ⟨4^k*left,boundary,some 4⟩ := by
  induction k generalizing left with
  | zero => simp [run]
  | succ k ih =>
    have ht : 2*(k+1) = 2+2*k := by omega
    rw [ht,Source284PayloadPop.run_add,pow_succ]
    have he : (4^k*4)*boundary = 4*(4^k*boundary) := by ring
    rw [he,back_pair,ih]
    simp [pow_succ]
    ring

theorem restore_boundary (continuation : Nat → Bool → Row) (left stream : Nat) :
    run (table continuation) ⟨left,2*stream+1,some 4⟩ 2 =
      ⟨left,2*stream,some 7⟩ := by
  simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> try split_ifs
  all_goals repeat' apply And.intro
  all_goals omega

/-- Reset every token, preserve the certificate and complete scratch half,
and enter the continuation after exactly `4*xs.length+6` source steps. -/
theorem clear (continuation : Nat → Bool → Row) (xs : List Bool) (certificate stream : Nat) :
    run (table continuation) ⟨pairTape xs certificate,2*stream,some 0⟩ (4*xs.length+6) =
      ⟨pairTape (List.replicate xs.length false) certificate,2*stream,some 7⟩ := by
  have ht : 4*xs.length+6 = 1+(2*xs.length+(3+(2*xs.length+2))) := by omega
  rw [ht,Source284PayloadPop.run_add _ _ 1 (2*xs.length+(3+(2*xs.length+2)))]
  change run (table continuation)
    (step (table continuation) ⟨pairTape xs certificate,2*stream,some 0⟩) _ = _
  rw [startup]
  unfold pairTape
  rw [Source284PayloadPop.run_add _ _ (2*xs.length) (3+(2*xs.length+2)),clear_pairs]
  rw [Source284PayloadPop.run_add _ _ 3 (2*xs.length+2),sentinel]
  rw [Source284PayloadPop.run_add _ _ (2*xs.length) 2,back_pairs,restore_boundary]
  have hp : 4^xs.length = 2^(2*xs.length) := by rw [Nat.pow_mul]
  rw [hp,← Source284ScratchSentinel.unaryPairs_stack,← Source284UnaryPairScanner.zero_pairTape]
  rfl

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  encode (7+states) (table continuation) 1

theorem source_clear (states : Nat) (continuation : Nat → Bool → Row)
    (xs : List Bool) (certificate stream : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (2*stream) (pairTape xs certificate)) (4*xs.length+6) =
      ⟨pairTape (List.replicate xs.length false) certificate,2*stream,active 7⟩ := by
  let c : Config := ⟨pairTape xs certificate,2*stream,some 0⟩
  have hvalid : Valid (7+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have hr := run_toSource (7+states) (table continuation) 1 c (closed states continuation hn hv) hvalid (4*xs.length+6)
  change Source284Relative.run (description states continuation)
    (Source284Relative.initial (2*stream) (pairTape xs certificate)) _ = _ at hr
  rw [hr]
  dsimp only [c]
  rw [clear]
  rfl

/-- The finite continuation runs after clearing, with every later transition
charged and the seven-state relocation recorded. -/
theorem source_clear_then (states : Nat) (continuation : Nat → Bool → Row)
    (xs : List Bool) (certificate stream fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    let c : Config := ⟨pairTape (List.replicate xs.length false) certificate,2*stream,some 0⟩
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (2*stream) (pairTape xs certificate)) (4*xs.length+6+fuel) =
      toSource (shiftConfig 7 (run continuation c fuel)) := by
  let initial : Config := ⟨pairTape xs certificate,2*stream,some 0⟩
  let c : Config := ⟨pairTape (List.replicate xs.length false) certificate,2*stream,some 0⟩
  have hvalid : Valid (7+states) initial := by intro q hq; simp [initial] at hq; subst q; omega
  have hr := run_toSource (7+states) (table continuation) 1 initial (closed states continuation hn hv)
    hvalid (4*xs.length+6+fuel)
  change Source284Relative.run (description states continuation)
    (Source284Relative.initial (2*stream) (pairTape xs certificate)) _ = _ at hr
  rw [hr,Source284PayloadPop.run_add]
  dsimp only [initial]
  rw [clear]
  change toSource (run (table continuation) (shiftConfig 7 c) fuel) = _
  rw [relocated_run]

namespace Fixtures
example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 22 1937) 18 =
      ⟨1920,22,active 7⟩ := by
  simpa [pairTape,scratch,bit] using source_clear states continuation [true,false,true] 7 11 hn hv
end Fixtures

end Shared.Beeping.NPcoNP.Source284UnaryClear
