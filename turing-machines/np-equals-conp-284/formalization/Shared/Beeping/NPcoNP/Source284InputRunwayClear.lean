import Shared.Beeping.NPcoNP.Source284FramedSerializeRunway

/-! Clear the known input-side sentinel behind two zero cells and return to
the original head position. The distant input suffix and joined prefix remain. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284InputRunwayClear

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q=0 then ⟨b,true,some 1⟩
  else if q=1 then ⟨b,false,some 2⟩
  else if q=2 then ⟨b,false,some 3⟩
  else if q=3 then ⟨false,true,some 4⟩
  else if q=4 then ⟨b,false,some 5⟩
  else if q=5 then ⟨b,false,some 6⟩
  else shiftRow 6 (continuation (q-6) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (6+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hs : q<6
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have he : (shiftRow 6 (continuation (q-6) b)).next=some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega,show q ≠ 2 by omega,
        show q ≠ 3 by omega,show q ≠ 4 by omega,show q ≠ 5 by omega] using hnext
    cases hh : (continuation (q-6) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hv (q-6) (by omega) b r hh
      simp [shiftRow,hh] at he; subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (6+q) b = shiftRow 6 (continuation q b) := by
  simp [table,show 6+q ≠ 1 by omega,show 6+q ≠ 2 by omega,show 6+q ≠ 3 by omega,
    show 6+q ≠ 4 by omega,show 6+q ≠ 5 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 6 c) = shiftConfig 6 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 6 c) fuel = shiftConfig 6 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem clear (continuation : Nat → Bool → Row) (tail right : Nat) :
    run (table continuation) ⟨4*(2*tail+1),right,some 0⟩ 6 =
      ⟨8*tail,right,some 6⟩ := by
  have h0 : step (table continuation) ⟨4*(2*tail+1),right,some 0⟩ =
      ⟨right,4*(2*tail+1),some 1⟩ := by
    apply Source284WindowRewind.generic_turn; intro b; simp [table]
  have h1 : step (table continuation) ⟨right,4*(2*tail+1),some 1⟩ =
      ⟨2*right,2*(2*tail+1),some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  have h2 : step (table continuation) ⟨2*right,2*(2*tail+1),some 2⟩ =
      ⟨4*right,2*tail+1,some 3⟩ := by
    simp [step,table,bit,Nat.testBit_zero] <;> omega
  have h3 : step (table continuation) ⟨4*right,2*tail+1,some 3⟩ =
      ⟨2*tail,4*right,some 4⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h4 : step (table continuation) ⟨2*tail,4*right,some 4⟩ =
      ⟨4*tail,2*right,some 5⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  have h5 : step (table continuation) ⟨4*tail,2*right,some 5⟩ =
      ⟨8*tail,right,some 6⟩ := by
    simp [step,table,bit,Nat.testBit_zero] <;> omega
  simp only [run,h0,h1,h2,h3,h4,h5]

theorem clear_then (continuation : Nat → Bool → Row) (tail right fuel : Nat) :
    run (table continuation) ⟨4*(2*tail+1),right,some 0⟩ (6+fuel) =
    shiftConfig 6 (run continuation ⟨8*tail,right,some 0⟩ fuel) := by
  rw [Source284ScratchScanner.run_add,clear]
  change run (table continuation) (shiftConfig 6 ⟨8*tail,right,some 0⟩) fuel = _
  exact relocated_run continuation _ fuel

end Shared.Beeping.NPcoNP.Source284InputRunwayClear
