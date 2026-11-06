import Shared.Beeping.NPcoNP.Source284DynamicGuardReveal
import Shared.Beeping.NPcoNP.Source284PopContinue
import Shared.Beeping.NPcoNP.Source284WitnessReframe

/-! Restore the raw source input frame after the dynamic witness guard.
The saved witness stays on the opposite half throughout. The result is a
finite source-table handoff, not yet the canonical pair serializer or a
physical-machine refinement. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284DynamicInputFrame

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource)

/-- Undo the one-cell marker transfer and create the zero boundary expected
by the existing flipped-stream normalizer. -/
def clearTable (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q=0 then ⟨b,true,some 1⟩
  else if q=1 then ⟨false,false,some 2⟩
  else if q=2 then ⟨b,true,some 3⟩
  else shiftRow 3 (continuation (q-3) b)

theorem clear_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (3+states) (clearTable continuation) := by
  intro q hq b q' hnext
  by_cases hs : q<3
  · interval_cases q <;> cases b <;> simp [clearTable] at hnext <;> omega
  · have he : (shiftRow 3 (continuation (q-3) b)).next=some q' := by
      simpa [clearTable,show q ≠ 0 by omega,show q ≠ 1 by omega,show q ≠ 2 by omega] using hnext
    cases ht : (continuation (q-3) b).next with
    | none => simp [shiftRow,ht] at he
    | some r =>
      have hr := hv (q-3) (by omega) b r ht
      simp [shiftRow,ht] at he
      subst q'
      omega

theorem clear_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    clearTable continuation (3+q) b = shiftRow 3 (continuation q b) := by
  simp [clearTable,show 3+q ≠ 1 by omega,show 3+q ≠ 2 by omega]

theorem clear_step (continuation : Nat → Bool → Row) (c : Config) :
    step (clearTable continuation) (shiftConfig 3 c) = shiftConfig 3 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,clear_row,shiftRow]
      split <;> rfl

theorem clear_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (clearTable continuation) (shiftConfig 3 c) fuel = shiftConfig 3 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,clear_step]

theorem clear_setup (continuation : Nat → Bool → Row) (saved stream : Nat) :
    run (clearTable continuation) ⟨2*saved+1,stream,some 0⟩ 3 =
      ⟨saved,2*stream,some 3⟩ := by
  have h0 : step (clearTable continuation) ⟨2*saved+1,stream,some 0⟩ =
      ⟨stream,2*saved+1,some 1⟩ := by
    apply Source284WindowRewind.generic_turn; intro b; simp [clearTable]
  have h1 : step (clearTable continuation) ⟨stream,2*saved+1,some 1⟩ =
      ⟨2*stream,saved,some 2⟩ := by
    simp [step,clearTable,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h2 : step (clearTable continuation) ⟨2*stream,saved,some 2⟩ =
      ⟨saved,2*stream,some 3⟩ := by
    apply Source284WindowRewind.generic_turn; intro b; simp [clearTable]
  simp only [run,h0,h1,h2]

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  clearTable (Source284ScratchNormalize.table (Source284PopContinue.table continuation))

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (139+states) (table continuation) := by
  have hp := Source284PopContinue.closed states continuation hn hv
  have hs := Source284WitnessReframe.closed (68+states) (Source284PopContinue.table continuation) (by omega) hp
  have hc := clear_closed (68+(68+states))
    (Source284ScratchNormalize.table (Source284PopContinue.table continuation)) (by omega) hs
  simpa [table,show 3+(68+(68+states))=139+states by omega] using hc

def cost (input : List Bool) : Nat :=
  3+(6*(input++[false]).length+11)+(4*(input++[false]).length+12)

theorem cost_formula (input : List Bool) : cost input = 10*input.length+36 := by
  simp [cost]
  omega

/-- The trailing loader dummy is removed, and the input frame is restored
with its exact retained high suffix. The witness half is unchanged except
for the explicit extra boundary zero introduced by normalization. -/
theorem reframe_then (states : Nat) (continuation : Nat → Bool → Row)
    (input : List Bool) (saved tail fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    run (table continuation) ⟨2*saved+1,flipped (input++[false]) tail,some 0⟩ (cost input+fuel) =
      shiftConfig 139 (run continuation
        ⟨2*saved,encodeFrame input (4*(2*tail+1)),some 0⟩ fuel) := by
  have ht : cost input+fuel = 3+((6*(input++[false]).length+11)+
      ((4*(input++[false]).length+12)+fuel)) := by simp [cost]; omega
  change run (clearTable (Source284ScratchNormalize.table (Source284PopContinue.table continuation)))
    ⟨2*saved+1,flipped (input++[false]) tail,some 0⟩ (cost input+fuel) = _
  rw [ht,Source284ScratchScanner.run_add,clear_setup]
  change run (clearTable (Source284ScratchNormalize.table (Source284PopContinue.table continuation)))
    (shiftConfig 3 ⟨saved,2*flipped (input++[false]) tail,some 0⟩) _ = _
  rw [clear_run,Source284WitnessReframe.normalize_then,
    Source284PopContinue.pop_then states continuation input false (2*saved) (2*tail+1) fuel hn hv]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  simp [bit]

def tail (k : Nat) (input : List Bool) (suffix : Nat) : Nat :=
  2^(Source284PositivePolynomialRunway.block k input.length)*
    Source284DelimitedPolynomialRunway.retained k input.length suffix

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284DynamicGuardReveal.description k (139+states) (table continuation)

/-- Starting from the original raw framed input and a successfully decoded
tagged certificate, the fixed finite source table restores the exact input
frame and preserves the saved witness frame for every continuation clock. -/
theorem decoded_input_frame (k states : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    ∃ witnessSuffix, certificate=4*encodeFrame witness witnessSuffix ∧ ∀ fuel,
      let limit := Source284DynamicGuardSource.bound k input.length
      let wf := encodeFrame witness (8*((witnessSuffix/4)/4)+1)
      let saved := 4*(4^(limit+1)*(2*wf))+1
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial (encodeFrame input suffix) certificate)
        (Source284GapUnarySource.totalCost k input+
          (Source284DynamicGuardReveal.revealCost limit witness+(cost input+fuel))) =
      lift (707+317*k+318+1+139) (Source284Relative.run (encode states continuation 1)
        ⟨2*saved,encodeFrame input (4*(2*tail k input suffix+1)),active 0⟩ fuel) := by
  have hc := closed states continuation hn hv
  obtain ⟨witnessSuffix,hcert,hreveal⟩ := Source284DynamicGuardReveal.decoded_reveal
    k (139+states) (table continuation) input witness certificate suffix (by omega) hc hdec
  refine ⟨witnessSuffix,hcert,?_⟩
  intro fuel
  let limit := Source284DynamicGuardSource.bound k input.length
  let wf := encodeFrame witness (8*((witnessSuffix/4)/4)+1)
  let saved := 4*(4^(limit+1)*(2*wf))+1
  let t := tail k input suffix
  have hr := hreveal (cost input+fuel)
  change Source284Relative.run (description k states continuation) _ _ =
    lift (707+317*k+318+1) (Source284Relative.run (encode (139+states) (table continuation) 1)
      ⟨2*saved+1,flipped (input++[false]) t,active 0⟩ (cost input+fuel)) at hr
  let c : Config := ⟨2*saved+1,flipped (input++[false]) t,some 0⟩
  have hvalid : Valid (139+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have hrun := run_toSource (139+states) (table continuation) 1 c hc hvalid (cost input+fuel)
  change Source284Relative.run (encode (139+states) (table continuation) 1)
    ⟨2*saved+1,flipped (input++[false]) t,active 0⟩ _ = _ at hrun
  have hstep := reframe_then states continuation input saved t fuel hn hv
  change run (table continuation) c (cost input+fuel) = _ at hstep
  rw [hrun,hstep,← lift_toSource,Source284SourceRelocation.lift_add] at hr
  let d : Config := ⟨2*saved,encodeFrame input (4*(2*t+1)),some 0⟩
  have hd : Valid states d := by intro q hq; simp [d] at hq; subst q; exact hn
  have hfinal := run_toSource states continuation 1 d hv hd fuel
  change Source284Relative.run (encode states continuation 1)
    ⟨2*saved,encodeFrame input (4*(2*t+1)),active 0⟩ fuel = _ at hfinal
  rw [← hfinal] at hr
  exact hr

namespace Fixtures
def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩

/-- The three paid transitions restore the zero boundary, even when the
saved witness half and input stream both contain one bits. -/
example : run (clearTable loop) ⟨15,11,some 0⟩ 3 = ⟨7,22,some 3⟩ := by decide +kernel

/-- Empty parsed input still follows the complete normalize-and-pop path. -/
example : run (table loop) ⟨15,2,some 0⟩ 36 = ⟨14,8,some 139⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284DynamicInputFrame
