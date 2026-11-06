import Shared.Beeping.NPcoNP.Source284PolynomialJoinedInput
import Shared.Beeping.NPcoNP.Source284FramedEncoder

/-! Connect the paid polynomial-workspace and valid-certificate join to the
existing guarded serializer's finite-window interface. The fixed table still
requires a bounded invalid-certificate path and physical refinement. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284PolynomialFramedEncoder

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284PolynomialJoinedInput (inputTail witnessTail)
open Shared.Beeping.NPcoNP.Source284FramedEncoderTable
open Shared.Beeping.NPcoNP.Source284FramedSerialize (rest body_reverse remaining out seedCost)
open Shared.Beeping.NPcoNP.Source284FramedEncoder (serialClock serialTime target)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Codes.BitNumeralCompare (value)
open Shared.Codes.FinitePrograms (Program Tape valid run initial)
open Shared.ComplexityBridge.TM2BinaryPostCosts (inputBits)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284PositivePolynomialRunway (block)
open Shared.Beeping.NPcoNP.Source284PolynomialMarkedCleanup (count)
open Shared.Beeping.NPcoNP.Source284BitWindow (Agree)

def sourceDescription {width : Nat} (enc : Codec width) (next : Program) (k : Nat) :=
  Source284PolynomialJoinedInput.description k (states enc next) (table enc next)

def sourceTime {width : Nat} (enc : Codec width) (k : Nat) (x w : List Bool) (fuel : Nat) :=
  Source284PolynomialJoinedInput.totalCost k x w+serialTime enc x w fuel

def inputList (k : Nat) (input : List Bool) (suffix : Nat) :=
  (4*inputTail k input.length suffix).bits

theorem input_left (k : Nat) (input : List Bool) (suffix : Nat) :
    stack [false] (value (inputList k input suffix)) = 8*inputTail k input.length suffix := by
  change 2*value ((4*inputTail k input.length suffix).bits) = _
  rw [Shared.Codes.BinaryAdditionCanonical.value_bits]
  ring

theorem input_suffix_zero (k : Nat) (input : List Bool) (suffix depth : Nat)
    (hfit : depth ≤ block k input.length) :
    2^depth ∣ value (inputList k input suffix).tail := by
  unfold inputList
  rw [← Nat.div2_bits_eq_tail,Shared.Codes.BinaryAdditionCanonical.value_bits]
  have h := Source284PolynomialJoinedInput.inputTail_zero k input.length suffix depth hfit
  simp only [Nat.div2_val]
  have he : 4*inputTail k input.length suffix/2 = 2*inputTail k input.length suffix := by omega
  rw [he]
  exact dvd_mul_of_dvd_right h 2

theorem serializer_seed_agree (k n suffix skip depth : Nat)
    (hfit : skip+depth ≤ count k n+3) :
    Agree depth (2*((2*(witnessTail k n suffix/2))/2^(skip+1))) 0 := by
  have hall := Source284PolynomialJoinedInput.witnessTail_zero k n suffix (skip+depth) hfit
  have hpref : 2^skip ∣ witnessTail k n suffix/2 :=
    dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hall
  have hd : 2^depth ∣ (witnessTail k n suffix/2)/2^skip := by
    apply (Nat.dvd_div_iff_mul_dvd hpref).2
    simpa [pow_add,Nat.mul_comm] using hall
  have he (t : Nat) : 2*t/2^(skip+1)=t/2^skip := by
    rw [pow_succ,Nat.mul_comm (2^skip) 2,Nat.mul_div_mul_left _ _ (by decide)]
  rw [he]
  have hm : 2^depth ∣ 2*((witnessTail k n suffix/2)/2^skip) := dvd_mul_of_dvd_right hd 2
  simp [Agree,Nat.mod_eq_zero_of_dvd hm]

/-- Exact raw-input source preparation followed by the existing finite
serializer reaches every specified continuing verifier window. -/
theorem source_continue_window {width : Nat} (enc : Codec width) (next : Program)
    (hn : valid next = true) (k : Nat) (x w : List Bool) (inputSuffix witnessSuffix radius fuel : Nat)
    (last : Shared.Codes.FinitePrograms.Config)
    (hnext : run next (0,Source284UntagOutputWindow.outputTape (out enc x w)
      (inputList k x inputSuffix).tail (processed (remaining x w) false).length) fuel = some (.inr last))
    (hfit : (word enc).length+(radius+serialClock enc x w fuel) ≤ count k x.length+3) :
    ∃ rev, Window radius
      (Source284Relative.run (sourceDescription enc next k)
        (Source284Relative.initial (encodeFrame x inputSuffix) (4*encodeFrame w witnessSuffix))
        (sourceTime enc k x w fuel))
      (Source284SourceRelocation.lift (1133+317*k) (target enc next last rev)) := by
  let L := inputList k x inputSuffix
  let tail := witnessTail k x.length witnessSuffix/2
  let t := serialTime enc x w fuel
  have hb := body_reverse x w
  have hblank := serializer_seed_agree k x.length witnessSuffix
    (word enc).length (radius+serialClock enc x w fuel) hfit
  have hw := Source284SerializerContinuePipeline.scan_seed_serializer_continue enc x w (rest x w) L false tail radius
    hb next hn fuel last hnext hblank
  obtain ⟨rev,hw⟩ := hw
  let c : Config := ⟨8*inputTail k x.length inputSuffix,
    stack (Source284JoinedFrames.joinedBits x w) tail,some 0⟩
  have hc : Valid (states enc next) c := by intro q hq; simp [c] at hq; subst q; exact states_pos enc next
  have hrun := run_toSource (states enc next) (table enc next) 1 c (closed enc next hn) hc t
  have hleft : stack [false] (value L) = 8*inputTail k x.length inputSuffix := input_left k x inputSuffix
  rw [hleft] at hw
  change Window radius (Source284Relative.run (encode (states enc next) (table enc next) 1) (toSource c) t)
    (target enc next last rev) at hw
  rw [hrun] at hw
  have hl := Source284SerializerStripWindow.lift_window radius (1133+317*k) _ _ hw
  rw [Source284SourceRelocation.lift_toSource] at hl
  have hs := Source284PolynomialJoinedInput.source_then k (states enc next) (table enc next)
    x w inputSuffix witnessSuffix t (states_pos enc next) (closed enc next hn)
  change Source284Relative.run (sourceDescription enc next k)
      (Source284Relative.initial (encodeFrame x inputSuffix) (4*encodeFrame w witnessSuffix))
      (sourceTime enc k x w fuel) = _ at hs
  rw [← hs] at hl
  exact ⟨rev,hl⟩

theorem source_encoder_window {width : Nat} (enc : Codec width) (next : Program)
    (hn : valid next = true) (k : Nat) (x w : List Bool) (inputSuffix witnessSuffix radiusSource radiusEncoder fuel q : Nat)
    (reference : Tape)
    (hrun : run next (initial (inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w))) fuel = some (.inr (q,reference)))
    (hinputFit : radiusEncoder+fuel-(2*(inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w)).length+3) ≤ block k x.length)
    (hwitnessFit : (word enc).length+(radiusSource+serialClock enc x w fuel) ≤ count k x.length+3) :
    ∃ actualTape rev revSource,
      Window radiusEncoder (represented actualTape rev (codeState q rev))
        (represented reference rev (codeState q rev)) ∧
      Window radiusSource
        (Source284Relative.run (sourceDescription enc next k)
          (Source284Relative.initial (encodeFrame x inputSuffix) (4*encodeFrame w witnessSuffix))
          (sourceTime enc k x w fuel))
        (Source284SourceRelocation.lift (1133+317*k) (target enc next (q,actualTape) revSource)) := by
  let L := inputList k x inputSuffix
  have hpad := input_suffix_zero k x inputSuffix _ hinputFit
  obtain ⟨actualTape,rev,hnext,henc⟩ := Source284SerializerEncoderSuffix.joined_output_live
    enc x w (rest x w) false L.tail (body_reverse x w) next hn fuel radiusEncoder q reference hrun hpad
  obtain ⟨revSource,hsource⟩ := source_continue_window enc next hn k x w inputSuffix witnessSuffix radiusSource fuel
    (q,actualTape) hnext hwitnessFit
  exact ⟨actualTape,rev,revSource,henc,hsource⟩

end Shared.Beeping.NPcoNP.Source284PolynomialFramedEncoder
