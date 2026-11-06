import Shared.Beeping.NPcoNP.Source284PopContinue
import Shared.Beeping.NPcoNP.Source284WitnessReframe

/-! Turn to the input-side flipped stream, normalize it, and remove its
explicit trailing false dummy. The witness frame remains on the opposite half. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284JoinedReframeAdapter

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q=0 then ⟨b,true,some 1⟩
  else if q=1 then ⟨b,false,some 2⟩
  else shiftRow 2 (Source284ScratchNormalize.table (Source284PopContinue.table continuation) (q-2) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (138+states) (table continuation) := by
  have h0 := Source284PopContinue.closed states continuation hn hv
  have h1 := Source284WitnessReframe.closed (68+states) (Source284PopContinue.table continuation) (by omega) h0
  intro q hq b q' hnext
  by_cases hs : q<2
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have he : (shiftRow 2 (Source284ScratchNormalize.table (Source284PopContinue.table continuation) (q-2) b)).next=some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega] using hnext
    cases hh : (Source284ScratchNormalize.table (Source284PopContinue.table continuation) (q-2) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := h1 (q-2) (by omega) b r hh
      simp [shiftRow,hh] at he; subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (2+q) b =
      shiftRow 2 (Source284ScratchNormalize.table (Source284PopContinue.table continuation) q b) := by
  simp [table,show 2+q ≠ 1 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 2 c) =
      shiftConfig 2 (step (Source284ScratchNormalize.table (Source284PopContinue.table continuation)) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 2 c) fuel =
      shiftConfig 2 (run (Source284ScratchNormalize.table (Source284PopContinue.table continuation)) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem setup (continuation : Nat → Bool → Row) (inputStream witnessFrame : Nat) :
    run (table continuation) ⟨4*inputStream,witnessFrame,some 0⟩ 2 =
      ⟨2*witnessFrame,2*inputStream,some 2⟩ := by
  have h0 : step (table continuation) ⟨4*inputStream,witnessFrame,some 0⟩ =
      ⟨witnessFrame,4*inputStream,some 1⟩ := by
    apply Source284WindowRewind.generic_turn; intro b; simp [table]
  have h1 : step (table continuation) ⟨witnessFrame,4*inputStream,some 1⟩ =
      ⟨2*witnessFrame,2*inputStream,some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  simp only [run,h0,h1]

def cost (x : List Bool) := 2+(6*(x++[false]).length+11)+(4*(x++[false]).length+12)

/-- The input-side dummy is removed after the normalizer; both framed lists
are exact, with their ignored high suffixes retained in explicit form. -/
theorem reframe_then (states : Nat) (continuation : Nat → Bool → Row)
    (x : List Bool) (tail witnessFrame fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    run (table continuation) ⟨4*flipped (x++[false]) tail,witnessFrame,some 0⟩ (cost x+fuel) =
    shiftConfig 138 (run continuation
      ⟨4*witnessFrame,encodeFrame x (4*(2*tail+1)),some 0⟩ fuel) := by
  have ht : cost x+fuel = 2+((6*(x++[false]).length+11)+
      ((4*(x++[false]).length+12)+fuel)) := by simp [cost]; omega
  rw [ht,Source284ScratchScanner.run_add,setup]
  change run (table continuation)
    (shiftConfig 2 ⟨2*witnessFrame,2*flipped (x++[false]) tail,some 0⟩) _ = _
  rw [relocated_run,Source284WitnessReframe.normalize_then]
  have he : 2*(2*witnessFrame)=4*witnessFrame := by omega
  rw [he,Source284PopContinue.pop_then states continuation x false (4*witnessFrame) (2*tail+1) fuel hn hv]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  simp [bit]

end Shared.Beeping.NPcoNP.Source284JoinedReframeAdapter
