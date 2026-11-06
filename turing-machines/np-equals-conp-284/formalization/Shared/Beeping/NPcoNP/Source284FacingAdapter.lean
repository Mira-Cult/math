import Shared.Beeping.NPcoNP.Source284TableRun
import Shared.Beeping.NPcoNP.Source284HardwireTable

/-! A paid one-transition initialization for a source table that expects its
certificate on the positive tape half. The source's ordinary input convention
starts with a blank positive half and certificate on the negative half. -/
namespace Shared.Beeping.NPcoNP.Source284FacingAdapter

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)

/-- State zero makes a preserving turn; all original states are shifted by
one. The adapter adds one logical state and one executed source transition. -/
def table (original : Nat → Bool → Row) (q : Nat) (read : Bool) : Row :=
  if q = 0 then ⟨read,true,some 1⟩ else shiftRow 1 (original (q-1) read)

theorem relocated_row (original : Nat → Bool → Row) (q : Nat) (read : Bool) :
    table original (1+q) read = shiftRow 1 (original q read) := by
  simp [table]

theorem relocated_step (original : Nat → Bool → Row) (c : Config) :
    step (table original) (shiftConfig 1 c) = shiftConfig 1 (step original c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig, Option.map_some, step, relocated_row, shiftRow]
      split <;> rfl

theorem relocated_run (original : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table original) (shiftConfig 1 c) fuel = shiftConfig 1 (run original c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem initial_step (original : Nat → Bool → Row) (certificate : Nat) :
    step (table original) ⟨certificate,0,some 0⟩ =
      shiftConfig 1 ⟨0,certificate,some 0⟩ := by
  simp [step,table,shiftConfig,bit]

theorem initial_run (original : Nat → Bool → Row) (certificate fuel : Nat) :
    run (table original) ⟨certificate,0,some 0⟩ (fuel+1) =
      shiftConfig 1 (run original ⟨0,certificate,some 0⟩ fuel) := by
  rw [run_front, initial_step, relocated_run]

theorem closed (original : Nat → Bool → Row) (n : Nat)
    (hn : 0 < n) (hclosed : Closed n original) : Closed (n+1) (table original) := by
  intro q hq read q' hnext
  by_cases hz : q = 0
  · subst q
    simp [table] at hnext
    omega
  · have hq' : q-1 < n := by omega
    simp only [table,if_neg hz,shiftRow] at hnext
    cases hr : (original (q-1) read).next with
    | none => simp [hr] at hnext
    | some r =>
        have hh := hclosed (q-1) hq' read r hr
        simp only [hr,Option.map_some,Option.some.injEq] at hnext
        omega

/-- Encoded source acceptance from the ordinary blank-input orientation
agrees with the original table after the paid initialization step. -/
theorem source_acceptance (original : Nat → Bool → Row) (n : Nat)
    (hn : 0 < n) (hclosed : Closed n original) (certificate fuel codeTail : Nat) :
    Shared.Beeping.NPcoNP.Source284Relative.accepts
      (encode (n+1) (table original) codeTail) 0 certificate (fuel+1) =
      (run original ⟨0,certificate,some 0⟩ fuel).state.isNone := by
  rw [bounded_acceptance (n+1) (table original) codeTail (by omega)
    (closed original n hn hclosed), initial_run]
  change ((run original ⟨0,certificate,some 0⟩ fuel).state.map (fun q => 1+q)).isNone = _
  cases h : (run original ⟨0,certificate,some 0⟩ fuel).state <;> simp [h]

end Shared.Beeping.NPcoNP.Source284FacingAdapter
