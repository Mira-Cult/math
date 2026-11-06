import Shared.Beeping.NPcoNP.Source284FramedSerializeTable

/-! Compose raw input preparation with the actual finite serializer, frame
removal and untagging table. The output is a proved finite tape window, with
an explicit quadratic-runway hypothesis. This is not yet a verifier run or a
physical-table beeper theorem. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284FramedSerialize

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)
open Shared.Beeping.NPcoNP.Source284CertificateJoin (witnessTail)
open Shared.Beeping.NPcoNP.Source284JoinedReframe (inputTail)
open Shared.Beeping.NPcoNP.Source284FramedSerializeTable
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Codes.BitNumeralCompare (value)
open Shared.Codes.FiniteProgramTaggedLoop (totalCost)
open Shared.Codes.FiniteProgramFrameLoop (padding)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284SerializerStrip (items)

def rest (x w : List Bool) := (Source284JoinedPrefixScan.joinedBody x w).reverse.tail

theorem body_reverse (x w : List Bool) :
    (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest x w := by
  obtain ⟨r,hr⟩ := Source284EncoderFirstSelection.body_reverse_starts_zero x w
  simp [rest,hr]

def remaining (x w : List Bool) := rest x w++[false]
def out {width : Nat} (enc : Codec width) (x w : List Bool) :=
  kept enc ++ (processed (remaining x w) false).flatMap (Source284EncoderFirstSelection.code enc)
def serialClock {width : Nat} (enc : Codec width) (x w : List Bool) :=
  totalCost (zero enc) (one enc) (remaining x w) false (kept enc)+2+
    (Shared.Codes.FiniteProgramFrameLoop.totalCost width (items enc (remaining x w))+2+
      (2+Shared.Codes.FiniteProgramUntag.cost (out enc x w).reverse))
def seedCost {width : Nat} (enc : Codec width) := 1+Source284HardwireTable.offset (word enc)+1
def serialTime {width : Nat} (enc : Codec width) (x w : List Bool) :=
  (Source284JoinedFrames.joinedBits x w).length+(seedCost enc+serialClock enc x w)

def sourceDescription {width : Nat} (enc : Codec width) (k : Nat) :=
  Source284FramedJoin.description k (states enc) (table enc)

def sourceTime {width : Nat} (enc : Codec width) (k : Nat) (x w : List Bool) :=
  Source284FramedJoin.totalCost k x w+serialTime enc x w

def inputList (k : Nat) (x : List Bool) (suffix : Nat) :=
  (2*(2*inputTail k x suffix+1)).bits

def target {width : Nat} (enc : Codec width) (x w L : List Bool) (rev : Bool) :=
  Source284SourceRelocation.lift (7+seedCost enc)
    (Source284SourceRelocation.lift (Source284DetectorExit.entry (rows enc).length)
      (represented (tapeAt
        (false::false::Shared.Codes.FiniteProgramUntag.padding (out enc x w).length (false::L.tail))
        (out enc x w++false::padding (processed (remaining x w) false).length [false,false]))
        rev (codeState ((Shared.Codes.FiniteProgramFrameUntag.pre width).length+14) rev)))

/-- The serialized joined input at the output of the finite source table.
The initial raw input and valid tagged witness are unmodified hypotheses;
all loader and serializer transitions are charged. -/
theorem source_serialize_window {width : Nat} (enc : Codec width)
    (k : Nat) (x w : List Bool) (inputSuffix witnessSuffix radius : Nat)
    (hfit : (word enc).length+(radius+serialClock enc x w) ≤
      firstZeros k x.length+2*x.length+4) :
    ∃ rev, Window radius
      (Source284Relative.run (sourceDescription enc k)
        (Source284Relative.initial (encodeFrame x inputSuffix) (4*encodeFrame w witnessSuffix))
        (sourceTime enc k x w))
      (Source284SourceRelocation.lift (1286+220*k) (target enc x w (inputList k x inputSuffix) rev)) := by
  let L := inputList k x inputSuffix
  let tail := witnessTail (firstZeros k x.length) x.length witnessSuffix/2
  let t := serialTime enc x w
  have hb := body_reverse x w
  have hblank := Source284FramedJoinPadding.serializer_seed_agree k x.length witnessSuffix
    (word enc).length (radius+serialClock enc x w) hfit
  have hw := Source284ClearFrameUntagPipeline.scan_seed_serialize_strip enc x w (rest x w) L false tail radius hb hblank
  obtain ⟨rev,hw⟩ := hw
  let c : Config := ⟨4*(2*inputTail k x inputSuffix+1),stack (Source284JoinedFrames.joinedBits x w) tail,some 0⟩
  have hc : Valid (states enc) c := by intro q hq; simp [c] at hq; subst q; exact states_pos enc
  have hrun := run_toSource (states enc) (table enc) 1 c (closed enc) hc t
  have hleft : stack [false] (value L) = 4*(2*inputTail k x inputSuffix+1) := by
    change 2*value ((2*(2*inputTail k x inputSuffix+1)).bits) = _
    rw [Shared.Codes.BinaryAdditionCanonical.value_bits]
    ring
  rw [hleft] at hw
  change Window radius (Source284Relative.run (encode (states enc) (table enc) 1) (toSource c) t) (target enc x w L rev) at hw
  rw [hrun] at hw
  have hl := Source284SerializerStripWindow.lift_window radius (1286+220*k) _ _ hw
  rw [Source284SourceRelocation.lift_toSource] at hl
  have hs := Source284FramedJoin.source_joined_then k (states enc) (table enc) x w witnessSuffix inputSuffix t
    (states_pos enc) (closed enc)
  change Source284Relative.run (sourceDescription enc k)
      (Source284Relative.initial (encodeFrame x inputSuffix) (4*encodeFrame w witnessSuffix))
      (sourceTime enc k x w) = _ at hs
  rw [← hs] at hl
  exact ⟨rev,hl⟩

end Shared.Beeping.NPcoNP.Source284FramedSerialize
