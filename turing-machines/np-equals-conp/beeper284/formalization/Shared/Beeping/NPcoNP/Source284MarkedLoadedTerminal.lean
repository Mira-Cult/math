import Shared.Beeping.NPcoNP.Source284MarkedFramedEncoder
import Shared.Beeping.NPcoNP.Source284FramedTerminal
import Shared.Beeping.NPcoNP.Source284UnliftWindow

/-! Transfer the final Boolean transition of the finite serializer/verifier
to the same dynamically guarded source description. The supplied window
and verifier step remain explicit; no physical table is asserted. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284MarkedLoadedTerminal

open Shared.Codes.FinitePrograms (Program Tape valid)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284FramedEncoderTable
open Shared.Beeping.NPcoNP.Source284FramedEncoder (serialTime target)
open Shared.Beeping.NPcoNP.Source284MarkedFramedEncoder (sourceDescription sourceTime)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource)

/-- The actual accepting or rejecting source transition agrees with the
corresponding finite verifier result once the one-cell window is established. -/
theorem loaded_terminal_step {width : Nat} (enc : Codec width) (p : Program)
    (k r : Nat) (x w : List Bool) (certificate inputSuffix fuel q : Nat)
    (t : Tape) (rev b : Bool) (hv : valid p = true) (hq : q < p.length)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k x.length) certificate = some w)
    (hr : Shared.Codes.FinitePrograms.step p (q,t) = some (.inl b))
    (hw : Window 1
      (Source284Relative.run (sourceDescription enc p k r)
        (Source284Relative.initial (encodeFrame x inputSuffix) certificate) (sourceTime enc k r x w fuel))
      (lift (1371+317*k+317*r+318+1+178+254+6) (target enc p (q,t) rev))) :
    ((Source284Relative.run (sourceDescription enc p k r)
      (Source284Relative.initial (encodeFrame x inputSuffix) certificate) (sourceTime enc k r x w fuel+1)).state == 0) = b := by
  let table' := table enc p
  let d := 1371+317*k+317*r+318+1+178+254+6
  obtain ⟨witnessSuffix,_,hjoined⟩ := Source284MarkedInputRunway.decoded_then
    k r (states enc p) table' x w certificate inputSuffix (states_pos enc p) (closed enc p hv) hdec
  let start : Config := ⟨8*Source284MarkedFramedEncoder.inputTail k r x inputSuffix,
    stack (Source284JoinedFrames.joinedBits x w)
      (Source284DynamicJoinedInput.witnessTail (Source284MarkedJoinedInput.enlargedLimit k r x.length) witnessSuffix),some 0⟩
  let a := run table' start (serialTime enc x w fuel)
  have hclosed : Closed (states enc p) table' := closed enc p hv
  have hstart : Valid (states enc p) start := by
    intro j hj
    change (some 0 : Option Nat) = some j at hj
    cases hj
    exact states_pos enc p
  have ha : Valid (states enc p) a := valid_run _ _ _ hclosed hstart _
  have hrun := run_toSource (states enc p) table' 1 start hclosed hstart (serialTime enc x w fuel)
  have hbefore := hjoined (serialTime enc x w fuel)
  change Source284Relative.run (sourceDescription enc p k r)
      (Source284Relative.initial (encodeFrame x inputSuffix) certificate) (sourceTime enc k r x w fuel) =
    lift d (Source284Relative.run (encode (states enc p) table' 1) (toSource start) (serialTime enc x w fuel)) at hbefore
  rw [hrun] at hbefore
  change Source284Relative.run (sourceDescription enc p k r)
      (Source284Relative.initial (encodeFrame x inputSuffix) certificate) (sourceTime enc k r x w fuel) =
    lift d (toSource a) at hbefore
  rw [hbefore] at hw
  have hinner : Window 1 (toSource a) (target enc p (q,t) rev) :=
    Source284UnliftWindow.window_reflect 1 d _ _ hw
  have hnext := Source284Relative.step_window (encode (states enc p) table' 1) 0
    (toSource a) (target enc p (q,t) rev) hinner
  have hresult := Source284FramedTerminal.serializer_terminal_step enc p q t rev b hv hq hr
  have hstep := step_toSource (states enc p) table' 1 a ha
  have hrun' := run_toSource (states enc p) table' 1 start hclosed hstart (serialTime enc x w fuel+1)
  have hafter := hjoined (serialTime enc x w fuel+1)
  have hclock : Source284MarkedInputRunway.cost k r x w+(serialTime enc x w fuel+1) =
      sourceTime enc k r x w fuel+1 := by unfold sourceTime; omega
  rw [hclock] at hafter
  change Source284Relative.run (sourceDescription enc p k r)
      (Source284Relative.initial (encodeFrame x inputSuffix) certificate) (sourceTime enc k r x w fuel+1) =
    lift d (Source284Relative.run (encode (states enc p) table' 1) (toSource start) (serialTime enc x w fuel+1)) at hafter
  rw [hrun'] at hafter
  change Source284Relative.run (sourceDescription enc p k r)
      (Source284Relative.initial (encodeFrame x inputSuffix) certificate) (sourceTime enc k r x w fuel+1) =
    lift d (toSource (step table' a)) at hafter
  rw [lift_toSource] at hafter
  rw [hafter,Source284FramedTerminal.shifted_acceptance,← hstep]
  have hstates := congrArg (fun s : Nat => s == 0) hnext.1
  rw [hstates]
  exact hresult

end Shared.Beeping.NPcoNP.Source284MarkedLoadedTerminal
