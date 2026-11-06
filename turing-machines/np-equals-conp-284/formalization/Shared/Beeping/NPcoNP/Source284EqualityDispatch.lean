import Shared.Beeping.NPcoNP.Source284EqualityReset

/-! The initialized retry program reaches continuation entry one on equality.
This finite dispatcher executes the first rewind transition at that entry;
its entry zero is an unused continuing sink in the all-input pipeline. -/
namespace Shared.Beeping.NPcoNP.Source284EqualityDispatch

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig shiftRow run_front)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 0⟩
  else if q = 1 then shiftRow 2 (Source284EqualityReset.table continuation 0 b)
  else shiftRow 2 (Source284EqualityReset.table continuation (q-2) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (23+states) (table continuation) := by
  have he := Source284EqualityReset.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; simp [table] at hnext; omega
  · by_cases h1 : q = 1
    · subst q
      have ht : (shiftRow 2 (Source284EqualityReset.table continuation 0 b)).next = some q' := by
        simpa [table] using hnext
      cases hnxt : (Source284EqualityReset.table continuation 0 b).next with
      | none => simp [shiftRow,hnxt] at ht
      | some r =>
        have h := he 0 (by omega) b r hnxt
        simp [shiftRow,hnxt] at ht
        subst q'
        omega
    · have ht : (shiftRow 2 (Source284EqualityReset.table continuation (q-2) b)).next = some q' := by
        simpa [table,h0,h1] using hnext
      have hq0 : q-2 < 21+states := by omega
      cases hnxt : (Source284EqualityReset.table continuation (q-2) b).next with
      | none => simp [shiftRow,hnxt] at ht
      | some r =>
        have h := he (q-2) hq0 b r hnxt
        simp [shiftRow,hnxt] at ht
        subst q'
        omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (2+q) b = shiftRow 2 (Source284EqualityReset.table continuation q b) := by
  have h0 : 2+q ≠ 0 := by omega
  have h1 : 2+q ≠ 1 := by omega
  simp [table,h0,h1]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 2 c) =
      shiftConfig 2 (step (Source284EqualityReset.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 2 c) fuel =
      shiftConfig 2 (run (Source284EqualityReset.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem enter (continuation : Nat → Bool → Row) (left right : Nat) :
    step (table continuation) ⟨left,right,some 1⟩ =
      shiftConfig 2 (step (Source284EqualityReset.table continuation) ⟨left,right,some 0⟩) := by
  simp [step,table,shiftConfig,shiftRow]
  split <;> rfl

theorem run_from_one (continuation : Nat → Bool → Row) (left right fuel : Nat) (hpos : 0 < fuel) :
    run (table continuation) ⟨left,right,some 1⟩ fuel =
      shiftConfig 2 (run (Source284EqualityReset.table continuation) ⟨left,right,some 0⟩ fuel) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
  rw [run_front,run_front,enter,relocated_run]

theorem reset_equal (continuation : Nat → Bool → Row) (w : List Bool) (certificate tail : Nat) :
    run (table continuation) ⟨2*pairTape (List.replicate w.length true) certificate,
      zeros w (flipped [false] tail),some 1⟩ (8*w.length+21) =
    ⟨pairTape (List.replicate w.length false) certificate,2*flipped (w++[false]) tail,some 23⟩ := by
  rw [run_from_one _ _ _ _ (by omega),Source284EqualityReset.reset_equal]
  rfl

/-- After the equality reset, the caller's finite continuation executes in
the same table; no further tape initialization is implicit. -/
theorem continuation_run (continuation : Nat → Bool → Row) (mode : Nat)
    (left right fuel : Nat) :
    run (table continuation) ⟨left,right,some (23+mode)⟩ fuel =
      shiftConfig 2 (shiftConfig 3 (shiftConfig 7 (shiftConfig 5 (shiftConfig 6
        (run continuation ⟨left,right,some mode⟩ fuel))))) := by
  let c : Config := ⟨left,right,some mode⟩
  have he : shiftConfig 2 (shiftConfig 3 (shiftConfig 7 (shiftConfig 5 (shiftConfig 6 c)))) =
      ⟨left,right,some (23+mode)⟩ := by simp [shiftConfig,c,← Nat.add_assoc]
  rw [← he,relocated_run]
  unfold Source284EqualityReset.table
  rw [Source284EqualityReset.relocated_run]
  unfold Source284MatchReset.table
  rw [Source284UnaryClear.relocated_run,Source284PayloadReset.relocated_run,
    Source284ScratchFlipReturn.relocated_run]

end Shared.Beeping.NPcoNP.Source284EqualityDispatch
