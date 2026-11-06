import Shared.Beeping.NPcoNP.Source284ScratchCompactLoop

/-! A paid finite table clears a known one immediately on the left and
returns the head and both tape orientations to their original boundary. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284SentinelClear

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q=0 then ⟨b,true,some 1⟩
  else if q=1 then ⟨false,false,some 2⟩
  else if q=2 then ⟨b,true,some 3⟩
  else if q=3 then ⟨b,false,some 4⟩
  else shiftRow 4 (continuation (q-4) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (4+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hs : q<4
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have he : (shiftRow 4 (continuation (q-4) b)).next=some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega,
        show q ≠ 2 by omega,show q ≠ 3 by omega] using hnext
    cases hh : (continuation (q-4) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hv (q-4) (by omega) b r hh
      simp [shiftRow,hh] at he; subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (4+q) b = shiftRow 4 (continuation q b) := by
  simp [table,show 4+q ≠ 1 by omega,show 4+q ≠ 2 by omega,show 4+q ≠ 3 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 4 c) = shiftConfig 4 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 4 c) fuel = shiftConfig 4 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem clear (continuation : Nat → Bool → Row) (left right : Nat) :
    run (table continuation) ⟨2*left+1,right,some 0⟩ 4 =
      ⟨2*left,right,some 4⟩ := by
  have h0 : step (table continuation) ⟨2*left+1,right,some 0⟩ =
      ⟨right,2*left+1,some 1⟩ := by
    apply Source284WindowRewind.generic_turn; intro b; simp [table]
  have h1 : step (table continuation) ⟨right,2*left+1,some 1⟩ =
      ⟨2*right,left,some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h2 : step (table continuation) ⟨2*right,left,some 2⟩ =
      ⟨left,2*right,some 3⟩ := by
    apply Source284WindowRewind.generic_turn; intro b; simp [table]
  have h3 : step (table continuation) ⟨left,2*right,some 3⟩ =
      ⟨2*left,right,some 4⟩ := by simp [step,table,bit,Nat.testBit_zero]
  simp only [run,h0,h1,h2,h3]

theorem clear_then (continuation : Nat → Bool → Row) (left right fuel : Nat) :
    run (table continuation) ⟨2*left+1,right,some 0⟩ (4+fuel) =
    shiftConfig 4 (run continuation ⟨2*left,right,some 0⟩ fuel) := by
  rw [Source284ScratchScanner.run_add,clear]
  change run (table continuation) (shiftConfig 4 ⟨2*left,right,some 0⟩) fuel = _
  exact relocated_run continuation _ fuel

end Shared.Beeping.NPcoNP.Source284SentinelClear
