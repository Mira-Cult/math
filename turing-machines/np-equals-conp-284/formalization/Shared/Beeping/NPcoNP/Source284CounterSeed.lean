import Shared.Beeping.NPcoNP.Source284OrientationHandoff
import Shared.Beeping.NPcoNP.Source284CountedShift

/-! Install the zero-length unary counter in an arbitrary ignored suffix.
Four paid source transitions overwrite the first suffix bit, restore the
head and orientation, and enter a supplied closed continuation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284CounterSeed

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨false,false,some 1⟩
  else if q = 1 then ⟨false,true,some 2⟩
  else shiftRow 2 (Source284OrientationHandoff.table 0 continuation (q-2) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (5+states) (table continuation) := by
  have hc := Source284OrientationHandoff.closed states 0 continuation hn hv
  intro q hq b q' hnext
  by_cases hsmall : q < 2
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have he : (shiftRow 2 (Source284OrientationHandoff.table 0 continuation (q-2) b)).next = some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega] using hnext
    cases hh : (Source284OrientationHandoff.table 0 continuation (q-2) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hc (q-2) (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (2+q) b = shiftRow 2 (Source284OrientationHandoff.table 0 continuation q b) := by
  simp [table,show 2+q ≠ 1 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 2 c) =
      shiftConfig 2 (step (Source284OrientationHandoff.table 0 continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 2 c) fuel =
      shiftConfig 2 (run (Source284OrientationHandoff.table 0 continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem initial_two (continuation : Nat → Bool → Row) (left higher : Nat) :
    run (table continuation) ⟨left,2*higher,some 0⟩ 2 =
      ⟨2*(higher/2),2*left,some 2⟩ := by
  simp [run,step,table,bit,Nat.testBit_zero] <;> omega

/-- The zero boundary and new counter delimiter are distinct cells. The
first old suffix bit is overwritten; all higher bits remain as `higher/2`. -/
theorem seed (continuation : Nat → Bool → Row) (left higher : Nat) :
    run (table continuation) ⟨left,2*higher,some 0⟩ 4 =
      ⟨left,2*counter 0 (higher/2),some 5⟩ := by
  rw [show 4 = 2+2 by decide,Source284PayloadPop.run_add,initial_two]
  change run (table continuation) (shiftConfig 2 ⟨2*(higher/2),2*left,some 0⟩) 2 = _
  rw [relocated_run]
  have h := Source284OrientationHandoff.two_steps 0 continuation true (2*(higher/2)) (2*left)
  simp [Source284OrientationHandoff.initialState,Source284OrientationHandoff.normalized] at h
  rw [h]
  simp [shiftConfig,Source284OrientationHandoff.normalized,counter]

/-- The seed then executes the supplied continuation without skipping any
steps; two relocations account for all five prefix states. -/
theorem seed_then (continuation : Nat → Bool → Row) (left higher fuel : Nat) :
    run (table continuation) ⟨left,2*higher,some 0⟩ (4+fuel) =
      shiftConfig 5 (run continuation ⟨left,2*counter 0 (higher/2),some 0⟩ fuel) := by
  rw [Source284PayloadPop.run_add,seed]
  change run (table continuation)
    (shiftConfig 2 (shiftConfig 3 ⟨left,2*counter 0 (higher/2),some 0⟩)) fuel = _
  rw [relocated_run,Source284OrientationHandoff.relocated_run]
  exact Source284SourceRelocation.shiftConfig_add 2 3 _

/-- Encoded source form, with every seed and continuation transition paid. -/
theorem source_seed_then (states : Nat) (continuation : Nat → Bool → Row)
    (left higher fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (5+states) (table continuation) 1)
      (Source284Relative.initial (2*higher) left) (4+fuel) =
      Source284SourceRelocation.lift 5
        (Source284Relative.run (encode states continuation 1)
          ⟨left,2*counter 0 (higher/2),active 0⟩ fuel) := by
  let start : Config := ⟨left,2*higher,some 0⟩
  have hvalid : Valid (5+states) start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource (5+states) (table continuation) 1 start (closed states continuation hn hv)
    hvalid (4+fuel)
  rw [seed_then,← Source284SourceRelocation.lift_toSource] at hr
  let finish : Config := ⟨left,2*counter 0 (higher/2),some 0⟩
  have hf : Valid states finish := by intro q hq; simp [finish] at hq; subst q; exact hn
  have hs := run_toSource states continuation 1 finish hv hf fuel
  rw [← hs] at hr
  exact hr

namespace Fixtures
def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
example : run (table loop) ⟨7,2*11,some 0⟩ 4 = ⟨7,20,some 5⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284CounterSeed
