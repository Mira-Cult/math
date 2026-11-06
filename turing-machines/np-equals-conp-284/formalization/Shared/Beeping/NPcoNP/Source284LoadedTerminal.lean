import Shared.Beeping.NPcoNP.Source284FramedTerminal
import Shared.Beeping.NPcoNP.Source284UnliftWindow

/-! The outer raw loader preserves the actual terminal step of its framed
continuation. The source window is a premise supplied by the predecessor
theorem; finite runway bounds and physical-table refinement are separate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284LoadedTerminal

open Shared.Codes.FinitePrograms (Program Tape valid)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284FramedEncoderTable
open Shared.Beeping.NPcoNP.Source284FramedEncoder
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284JoinedReframe (inputTail)
open Shared.Beeping.NPcoNP.Source284CertificateJoin (witnessTail)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)

/-- A matching one-cell window just before a verifier terminal row determines
the result of the next actual source step, even with arbitrary higher cells. -/
theorem loaded_terminal_step {width : Nat} (enc : Codec width) (p : Program)
    (k : Nat) (x w : List Bool) (witnessSuffix inputSuffix fuel q : Nat)
    (t : Tape) (rev b : Bool) (hv : valid p = true) (hq : q < p.length)
    (hr : Shared.Codes.FinitePrograms.step p (q,t) = some (.inl b))
    (hw : Window 1
      (Source284Relative.run (sourceDescription enc p k)
        (Source284Relative.initial (encodeFrame x inputSuffix) (4*encodeFrame w witnessSuffix))
        (sourceTime enc k x w fuel))
      (Source284SourceRelocation.lift (1292+220*k) (target enc p (q,t) rev))) :
    ((Source284Relative.run (sourceDescription enc p k)
      (Source284Relative.initial (encodeFrame x inputSuffix) (4*encodeFrame w witnessSuffix))
      (sourceTime enc k x w fuel+1)).state == 0) = b := by
  let table' := table enc p
  let start : Config := ⟨8*inputTail k x inputSuffix,
    stack (Source284JoinedFrames.joinedBits x w)
      (witnessTail (firstZeros k x.length) x.length witnessSuffix/2),some 0⟩
  let a := run table' start (serialTime enc x w fuel)
  let d := 1292+220*k
  have hclosed : Closed (states enc p) table' := closed enc p hv
  have hstart : Valid (states enc p) start := by
    intro j hj
    simp [start] at hj
    subst j
    exact states_pos enc p
  have ha : Valid (states enc p) a := valid_run _ _ _ hclosed hstart _
  have hzero := Source284InputRunway.source_then k (states enc p) table' x w
    witnessSuffix inputSuffix (serialTime enc x w fuel) (states_pos enc p) hclosed
  have hbefore : Source284Relative.run (sourceDescription enc p k)
      (Source284Relative.initial (encodeFrame x inputSuffix) (4*encodeFrame w witnessSuffix))
      (sourceTime enc k x w fuel) = toSource (shiftConfig d a) := by
    simpa [sourceDescription,sourceTime,a,start,table',d] using hzero
  rw [hbefore,← Source284SourceRelocation.lift_toSource] at hw
  have hinner : Window 1 (toSource a) (target enc p (q,t) rev) :=
    Source284UnliftWindow.window_reflect 1 d _ _ hw
  have hnext := Source284Relative.step_window (encode (states enc p) table' 1) 0
    (toSource a) (target enc p (q,t) rev) hinner
  have hresult := Source284FramedTerminal.serializer_terminal_step enc p q t rev b hv hq hr
  have hstep := step_toSource (states enc p) table' 1 a ha
  have hone := Source284InputRunway.source_then k (states enc p) table' x w
    witnessSuffix inputSuffix (serialTime enc x w fuel+1) (states_pos enc p) hclosed
  have hafter : Source284Relative.run (sourceDescription enc p k)
      (Source284Relative.initial (encodeFrame x inputSuffix) (4*encodeFrame w witnessSuffix))
      (sourceTime enc k x w fuel+1) = toSource (shiftConfig d (step table' a)) := by
    simpa [sourceDescription,sourceTime,a,start,table',d,run,Nat.add_assoc] using hone
  rw [hafter,Source284FramedTerminal.shifted_acceptance,← hstep]
  have hstates := congrArg (fun s : Nat => s == 0) hnext.1
  rw [hstates]
  exact hresult

end Shared.Beeping.NPcoNP.Source284LoadedTerminal
