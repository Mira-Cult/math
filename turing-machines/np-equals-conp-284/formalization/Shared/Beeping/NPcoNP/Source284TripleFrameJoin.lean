import Shared.Beeping.NPcoNP.Source284JoinedFrames

/-! Turn from adjacent framed input and witness to the already checked
three-zero joined-prefix table, paying for all four boundary transitions. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284TripleFrameJoin

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q=0 then ⟨b,true,some 1⟩
  else if q=1 then ⟨b,false,some 2⟩
  else if q=2 then ⟨true,false,some 3⟩
  else if q=3 then ⟨b,false,some 4⟩
  else shiftRow 4 (Source284JoinedFrames.table continuation (q-4) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (20+states) (table continuation) := by
  have h0 := Source284JoinedFrames.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases hs : q<4
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have he : (shiftRow 4 (Source284JoinedFrames.table continuation (q-4) b)).next=some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega,
        show q ≠ 2 by omega,show q ≠ 3 by omega] using hnext
    cases hh : (Source284JoinedFrames.table continuation (q-4) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := h0 (q-4) (by omega) b r hh
      simp [shiftRow,hh] at he; subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (4+q) b = shiftRow 4 (Source284JoinedFrames.table continuation q b) := by
  simp [table,show 4+q ≠ 1 by omega,show 4+q ≠ 2 by omega,show 4+q ≠ 3 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 4 c) =
      shiftConfig 4 (step (Source284JoinedFrames.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 4 c) fuel =
      shiftConfig 4 (run (Source284JoinedFrames.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem setup (continuation : Nat → Bool → Row) (inputFrame witnessFrame : Nat) :
    run (table continuation) ⟨8*witnessFrame,inputFrame,some 0⟩ 4 =
      ⟨2*(4*inputFrame+1),witnessFrame,some 4⟩ := by
  have h0 : step (table continuation) ⟨8*witnessFrame,inputFrame,some 0⟩ =
      ⟨inputFrame,8*witnessFrame,some 1⟩ := by
    apply Source284WindowRewind.generic_turn; intro b; simp [table]
  have h1 : step (table continuation) ⟨inputFrame,8*witnessFrame,some 1⟩ =
      ⟨2*inputFrame,4*witnessFrame,some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  have h2 : step (table continuation) ⟨2*inputFrame,4*witnessFrame,some 2⟩ =
      ⟨4*inputFrame+1,2*witnessFrame,some 3⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  have h3 : step (table continuation) ⟨4*inputFrame+1,2*witnessFrame,some 3⟩ =
      ⟨2*(4*inputFrame+1),witnessFrame,some 4⟩ := by
    simp [step,table,bit,Nat.testBit_zero] <;> omega
  simp only [run,h0,h1,h2,h3]

theorem join_then (continuation : Nat → Bool → Row) (x w : List Bool)
    (inputSuffix witnessTail fuel : Nat) :
    run (table continuation) ⟨8*encodeFrame w (2*witnessTail+1),encodeFrame x inputSuffix,some 0⟩
      ((2*x.length+10)+fuel) =
    shiftConfig 20 (run continuation
      ⟨inputSuffix,stack (Source284JoinedFrames.joinedBits x w) witnessTail,some 0⟩ fuel) := by
  have ht : 2*x.length+10+fuel = 4+((2*x.length+6)+fuel) := by omega
  rw [ht,Source284ScratchScanner.run_add,setup]
  change run (table continuation) (shiftConfig 4
    ⟨2*(4*encodeFrame x inputSuffix+1),encodeFrame w (2*witnessTail+1),some 0⟩) _ = _
  rw [relocated_run,Source284JoinedFrames.join_then,Source284JoinedFrames.joined_stack,
    Source284SourceRelocation.shiftConfig_add]

end Shared.Beeping.NPcoNP.Source284TripleFrameJoin
