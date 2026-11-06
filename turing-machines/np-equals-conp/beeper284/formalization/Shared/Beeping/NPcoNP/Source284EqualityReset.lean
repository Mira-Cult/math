import Shared.Beeping.NPcoNP.Source284MatchReset

/-! The equality branch has just crossed the scratch boundary. This finite
three-step adapter returns to it, then resets both marker tracks, producing
unmarked payload and exactly payload-length many zero unary pairs. -/
namespace Shared.Beeping.NPcoNP.Source284EqualityReset

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig shiftRow)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def rewind (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else if q = 2 then ⟨b,true,some 3⟩
  else shiftRow 3 (continuation (q-3) b)

theorem rewind_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (3+states) (rewind continuation) := by
  intro q hq b q' hnext
  by_cases hsmall : q < 3
  · interval_cases q <;> cases b <;> simp [rewind] at hnext <;> omega
  · have h0 : q ≠ 0 := by omega
    have h1 : q ≠ 1 := by omega
    have h2 : q ≠ 2 := by omega
    have ht : (shiftRow 3 (continuation (q-3) b)).next = some q' := by
      simpa [rewind,h0,h1,h2] using hnext
    have hq0 : q-3 < states := by omega
    cases he : (continuation (q-3) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hv (q-3) hq0 b r he
      simp [shiftRow,he] at ht
      subst q'
      omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    rewind continuation (3+q) b = shiftRow 3 (continuation q b) := by
  have h0 : 3+q ≠ 0 := by omega
  have h1 : 3+q ≠ 1 := by omega
  have h2 : 3+q ≠ 2 := by omega
  simp [rewind,h0,h1,h2]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (rewind continuation) (shiftConfig 3 c) = shiftConfig 3 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (rewind continuation) (shiftConfig 3 c) fuel = shiftConfig 3 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem rewind_boundary (continuation : Nat → Bool → Row) (left stream : Nat) :
    run (rewind continuation) ⟨2*left,stream,some 0⟩ 3 = ⟨left,2*stream,some 3⟩ := by
  simp [run,step,rewind,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> try split_ifs
  all_goals repeat' constructor
  all_goals omega

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  rewind (Source284MatchReset.table continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (21+states) (table continuation) := by
  have hm := Source284MatchReset.closed states continuation hn hv
  have hr := rewind_closed (18+states) (Source284MatchReset.table continuation) (by omega) hm
  have he : 3+(18+states) = 21+states := by omega
  rw [he] at hr
  exact hr

/-- Equality output is rewound and reset in exactly `8*n+21` steps. -/
theorem reset_equal (continuation : Nat → Bool → Row) (w : List Bool) (certificate tail : Nat) :
    run (table continuation) ⟨2*pairTape (List.replicate w.length true) certificate,
      zeros w (flipped [false] tail),some 0⟩ (8*w.length+21) =
    ⟨pairTape (List.replicate w.length false) certificate,2*flipped (w++[false]) tail,some 21⟩ := by
  have ht : 8*w.length+21 = 3+((4*(List.replicate w.length true).length+6)+(4*(w.length+0)+12)) := by simp; omega
  rw [ht,run_add]
  unfold table
  rw [rewind_boundary]
  change run (rewind (Source284MatchReset.table continuation))
    (shiftConfig 3 ⟨pairTape (List.replicate w.length true) certificate,
      2*zeros w (flipped ([]++[false]) tail),some 0⟩) _ = _
  have hm := Source284MatchReset.reset continuation (List.replicate w.length true) w [] certificate tail
  simp only [List.length_nil] at hm
  rw [relocated_run,hm]
  simp [shiftConfig]

end Shared.Beeping.NPcoNP.Source284EqualityReset
