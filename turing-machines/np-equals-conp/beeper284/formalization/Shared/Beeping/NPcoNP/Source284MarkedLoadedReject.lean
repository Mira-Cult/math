import Shared.Beeping.NPcoNP.Source284MarkedLoadedTerminal
import Shared.Beeping.NPcoNP.Source284FramedRejectSink

/-! A false finite-verifier result enters its real stable reject sink in the
same dynamically guarded source description. This is not an argument from a
finite nonacceptance observation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284MarkedLoadedReject

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

theorem loaded_false_stable {width : Nat} (enc : Codec width) (p : Program)
    (k r : Nat) (x w : List Bool) (certificate inputSuffix fuel q : Nat)
    (t : Tape) (rev : Bool) (hv : valid p = true) (hq : q < p.length)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k x.length) certificate = some w)
    (hr : Shared.Codes.FinitePrograms.step p (q,t) = some (.inl false))
    (hw : Window 1
      (Source284Relative.run (sourceDescription enc p k r)
        (Source284Relative.initial (encodeFrame x inputSuffix) certificate) (sourceTime enc k r x w fuel))
      (lift (1371+317*k+317*r+318+1+178+254+6) (target enc p (q,t) rev))) :
    ∀ extra,
      ((Source284Relative.run (sourceDescription enc p k r)
        (Source284Relative.initial (encodeFrame x inputSuffix) certificate)
        (sourceTime enc k r x w fuel+1+extra)).state == 0) = false := by
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
  have hreject := Source284FramedRejectSink.serializer_terminal_reject enc p q t rev hv hq hr
  have hstep := step_toSource (states enc p) table' 1 a ha
  have hstate : (toSource (step table' a)).state = active (Source284FramedRejectSink.sink enc p) := by
    rw [← hstep]
    exact hnext.1.trans hreject
  have hsink : (step table' a).state = some (Source284FramedRejectSink.sink enc p) :=
    Source284FramedRejectSink.toSource_state_reflect _ _ hstate
  intro extra
  have hstable := Source284FramedRejectSink.sink_run enc p (step table' a) hsink extra
  have hrun' := run_toSource (states enc p) table' 1 start hclosed hstart (serialTime enc x w fuel+1+extra)
  have hone := hjoined (serialTime enc x w fuel+1+extra)
  change Source284Relative.run (sourceDescription enc p k r)
      (Source284Relative.initial (encodeFrame x inputSuffix) certificate)
      (Source284MarkedInputRunway.cost k r x w+(serialTime enc x w fuel+1+extra)) =
    lift d (Source284Relative.run (encode (states enc p) table' 1) (toSource start)
      (serialTime enc x w fuel+1+extra)) at hone
  have hclock : Source284MarkedInputRunway.cost k r x w+(serialTime enc x w fuel+1+extra) =
      sourceTime enc k r x w fuel+1+extra := by simp [sourceTime]; omega
  rw [hclock] at hone
  rw [hrun'] at hone
  have hafter : Source284Relative.run (sourceDescription enc p k r)
      (Source284Relative.initial (encodeFrame x inputSuffix) certificate) (sourceTime enc k r x w fuel+1+extra) =
      toSource (shiftConfig d (run table' (step table' a) extra)) := by
    simpa [a,Source284ScratchFlipReturn.run_add,run,Nat.add_assoc,lift_toSource] using hone
  rw [hafter,Source284FramedTerminal.shifted_acceptance]
  change ((nextState (run table' (step table' a) extra).state) == 0) = false
  rw [hstable]
  simp [nextState,active]

end Shared.Beeping.NPcoNP.Source284MarkedLoadedReject
