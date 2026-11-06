import Shared.Beeping.NPcoNP.Source284InputRunway
import Shared.Beeping.NPcoNP.Source284SerializerEncoderSuffix

/-! Compose raw preparation, paid input-marker cleanup, serializer, untagger,
and an arbitrary supplied finite encoder prefix. Window hypotheses are
explicit; no physical-machine refinement is asserted. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284FramedEncoder

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)
open Shared.Beeping.NPcoNP.Source284CertificateJoin (witnessTail)
open Shared.Beeping.NPcoNP.Source284JoinedReframe (inputTail)
open Shared.Beeping.NPcoNP.Source284FramedEncoderTable
open Shared.Beeping.NPcoNP.Source284FramedSerialize (rest body_reverse remaining out seedCost)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Codes.BitNumeralCompare (value)
open Shared.Codes.FinitePrograms (Program Tape valid)
open Shared.Codes.FinitePrograms (run initial)
open Shared.ComplexityBridge.TM2BinaryPostCosts (inputBits)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)

def serialClock {width : Nat} (enc : Codec width) (x w : List Bool) (fuel : Nat) :=
  Shared.Codes.FiniteProgramTaggedLoop.totalCost (zero enc) (one enc) (remaining x w) false (kept enc)+2+
    (Shared.Codes.FiniteProgramFrameLoop.totalCost width (Source284SerializerStrip.items enc (remaining x w))+2+
      (2+Shared.Codes.FiniteProgramUntag.cost (out enc x w).reverse)+2+fuel)

def serialTime {width : Nat} (enc : Codec width) (x w : List Bool) (fuel : Nat) :=
  (Source284JoinedFrames.joinedBits x w).length+(seedCost enc+serialClock enc x w fuel)

def sourceDescription {width : Nat} (enc : Codec width) (next : Program) (k : Nat) :=
  Source284InputRunway.description k (states enc next) (table enc next)

def sourceTime {width : Nat} (enc : Codec width) (k : Nat) (x w : List Bool) (fuel : Nat) :=
  Source284InputRunway.preparationTime k x w+serialTime enc x w fuel

def target {width : Nat} (enc : Codec width) (next : Program) (last : Shared.Codes.FinitePrograms.Config) (rev : Bool) :=
  Source284SourceRelocation.lift (7+seedCost enc)
    (Source284SourceRelocation.lift (Source284DetectorExit.entry (rows enc).length)
      (represented last.2 rev (codeState
        ((Shared.Codes.FiniteProgramFrameUntag.program width).length+2+last.1) rev)))

/-- Given an actual continuing finite-program run on the untagged output,
the single raw source table reaches the corresponding finite tape window. -/
theorem source_continue_window {width : Nat} (enc : Codec width) (next : Program)
    (hn : valid next = true) (k : Nat) (x w : List Bool) (inputSuffix witnessSuffix radius fuel : Nat)
    (last : Shared.Codes.FinitePrograms.Config)
    (hnext : run next (0,Source284UntagOutputWindow.outputTape (out enc x w)
      (Source284InputRunway.inputList k x inputSuffix).tail (processed (remaining x w) false).length) fuel = some (.inr last))
    (hfit : (word enc).length+(radius+serialClock enc x w fuel) ≤
      firstZeros k x.length+2*x.length+4) :
    ∃ rev, Window radius
      (Source284Relative.run (sourceDescription enc next k)
        (Source284Relative.initial (encodeFrame x inputSuffix) (4*encodeFrame w witnessSuffix))
        (sourceTime enc k x w fuel))
      (Source284SourceRelocation.lift (1292+220*k) (target enc next last rev)) := by
  let L := Source284InputRunway.inputList k x inputSuffix
  let tail := witnessTail (firstZeros k x.length) x.length witnessSuffix/2
  let t := serialTime enc x w fuel
  have hb := body_reverse x w
  have hblank := Source284FramedJoinPadding.serializer_seed_agree k x.length witnessSuffix
    (word enc).length (radius+serialClock enc x w fuel) hfit
  have hw := Source284SerializerContinuePipeline.scan_seed_serializer_continue enc x w (rest x w) L false tail radius
    hb next hn fuel last hnext hblank
  obtain ⟨rev,hw⟩ := hw
  let c : Source284TableRun.Config := ⟨8*inputTail k x inputSuffix,
    stack (Source284JoinedFrames.joinedBits x w) tail,some 0⟩
  have hc : Valid (states enc next) c := by intro q hq; simp [c] at hq; subst q; exact states_pos enc next
  have hrun := run_toSource (states enc next) (table enc next) 1 c (closed enc next hn) hc t
  have hleft : stack [false] (value L) = 8*inputTail k x inputSuffix :=
    Source284InputRunway.input_left k x inputSuffix
  rw [hleft] at hw
  change Window radius (Source284Relative.run (encode (states enc next) (table enc next) 1) (toSource c) t)
    (target enc next last rev) at hw
  rw [hrun] at hw
  have hl := Source284SerializerStripWindow.lift_window radius (1292+220*k) _ _ hw
  rw [Source284SourceRelocation.lift_toSource] at hl
  have hs := Source284InputRunway.source_then k (states enc next) (table enc next) x w witnessSuffix inputSuffix t
    (states_pos enc next) (closed enc next hn)
  change Source284Relative.run (sourceDescription enc next k)
      (Source284Relative.initial (encodeFrame x inputSuffix) (4*encodeFrame w witnessSuffix))
      (sourceTime enc k x w fuel) = _ at hs
  rw [← hs] at hl
  exact ⟨rev,hl⟩

/-- If the reference finite encoder has a continuing run and both explicitly
charged zero runways are large enough, the actual raw source execution reaches
an agreeing finite encoder window. -/
theorem source_encoder_window {width : Nat} (enc : Codec width) (next : Program)
    (hn : valid next = true) (k : Nat) (x w : List Bool) (inputSuffix witnessSuffix radiusSource radiusEncoder fuel q : Nat)
    (reference : Tape)
    (hrun : run next (initial (inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w))) fuel = some (.inr (q,reference)))
    (hinputFit : radiusEncoder+fuel-(2*(inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w)).length+3) ≤ k*(x.length*x.length)+2)
    (hwitnessFit : (word enc).length+(radiusSource+serialClock enc x w fuel) ≤
      firstZeros k x.length+2*x.length+4) :
    ∃ actualTape rev revSource,
      Window radiusEncoder (represented actualTape rev (codeState q rev))
        (represented reference rev (codeState q rev)) ∧
      Window radiusSource
        (Source284Relative.run (sourceDescription enc next k)
          (Source284Relative.initial (encodeFrame x inputSuffix) (4*encodeFrame w witnessSuffix))
          (sourceTime enc k x w fuel))
        (Source284SourceRelocation.lift (1292+220*k) (target enc next (q,actualTape) revSource)) := by
  let L := Source284InputRunway.inputList k x inputSuffix
  have hpad := Source284InputRunway.input_suffix_zero k x inputSuffix _ hinputFit
  obtain ⟨actualTape,rev,hnext,henc⟩ := Source284SerializerEncoderSuffix.joined_output_live
    enc x w (rest x w) false L.tail (body_reverse x w) next hn fuel radiusEncoder q reference hrun hpad
  obtain ⟨revSource,hsource⟩ := source_continue_window enc next hn k x w inputSuffix witnessSuffix radiusSource fuel
    (q,actualTape) hnext hwitnessFit
  exact ⟨actualTape,rev,revSource,henc,hsource⟩

end Shared.Beeping.NPcoNP.Source284FramedEncoder
