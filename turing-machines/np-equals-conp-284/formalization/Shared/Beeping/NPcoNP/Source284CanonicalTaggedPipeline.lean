import Shared.Beeping.NPcoNP.Source284DecodedTaggedPipeline
import Shared.Beeping.NPcoNP.Source284OffsetExactHandoff

/-! Canonical witness frames have a fixed sentinel suffix. The existing
source decoder removes that suffix from scratch, so no zero-window size
hypothesis is needed for this completeness-side path. High aliases remain a
separate soundness obligation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284CanonicalTaggedPipeline

open Shared.Codes.BitNumeralCompare (value)
open Shared.Codes.FiniteProgramTaggedLoop (result)
open Shared.Codes.FiniteProgramFrameLoop (padding)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284TableEncode (encode active)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284OrientedExit (entry)
open Shared.Beeping.NPcoNP.Source284EncoderFirstSelection (code)
open Shared.Beeping.NPcoNP.Source284EncoderMarkerSeed (marker)
open Shared.Beeping.NPcoNP.Source284DecodedTaggedPipeline

/-- A fixed framed payload uniquely determines its remaining suffix. -/
theorem frame_suffix_injective (w : List Bool) :
    Function.Injective (Source284Parser.encodeFrame w) := by
  induction w with
  | nil =>
    intro a b h
    simp only [Source284Parser.encodeFrame] at h
    omega
  | cons v vs ih =>
    intro a b h
    apply ih
    have ha : Source284Parser.encodeFrame (v::vs) a / 4 = Source284Parser.encodeFrame vs a := by
      cases v <;> simp [Source284Parser.encodeFrame] <;> omega
    have hb : Source284Parser.encodeFrame (v::vs) b / 4 = Source284Parser.encodeFrame vs b := by
      cases v <;> simp [Source284Parser.encodeFrame] <;> omega
    rw [← ha,← hb,h]

/-- The canonical tagged witness leaves zero in the scratch tail selected by
the existing source decoder. -/
theorem canonical_suffix (w : List Bool) (suffix : Nat)
    (h : Source284TaggedWitnessCodec.encode w = 4*Source284Parser.encodeFrame w suffix) :
    suffix = 1 := by
  have hc := Source284OffsetExactHandoff.canonical_tagged_frame w
  have he : Source284Parser.encodeFrame w 1 = Source284Parser.encodeFrame w suffix := by omega
  exact (frame_suffix_injective w he).symm

/-- For every bounded witness, the actual decoded-source pipeline reaches the
metadata-free output window for any requested radius. This uses the canonical
certificate, not an arbitrary high-bit alias, and still starts with the
prepared unary bound required by the decoded source. -/
theorem canonical_to_stripped_window {width : Nat} (enc : Codec width)
    (limit input : Nat) (w rest : List Bool) (k : Nat) (hw : w.length ≤ limit)
    (hbody : (Source284JoinedPrefixScan.joinedBody (Source284RawParse.payload input.bits) w).reverse = false::rest) :
    ∃ inputSuffix,
      input = Source284Parser.encodeFrame (Source284RawParse.payload input.bits) inputSuffix ∧
      ∃ rev', Window k
        (Source284Relative.run (description enc)
          (Source284Relative.initial (Source284TaggedWitnessCodec.encode w)
            (Source284UnaryPairScanner.pairTape (List.replicate limit false) input))
          (prefixCost limit input w+
            ((Source284JoinedFrames.joinedBits (Source284RawParse.payload input.bits) w).length+
              (seedCost enc+clock enc rest))))
        (let remaining := rest++[true]
         let b := (result (code enc false) (code enc true) remaining false (marker enc)).1
         let L := (inputSuffix/4).bits
         let out := marker enc ++ (processed remaining false).flatMap (code enc)
         Source284SourceRelocation.lift 782
          (Source284SourceRelocation.lift (7+seedCost enc)
           (Source284SourceRelocation.lift (entry (serializerStates enc))
            (represented (tapeAt (cursor b L out).2
              ((cursor b L out).1::false::false::padding (processed remaining false).length [false,false]))
              rev' (codeState (Shared.Codes.FiniteProgramFrameLoop.empty width) rev'))))) := by
  have hdec := Source284TaggedWitnessCodec.decode_encode limit w hw
  obtain ⟨ws,is,hcert,hinput,hr⟩ := Source284JoinedFrames.decoded_join_then
    (scanStates enc) (scanTable enc) limit (Source284TaggedWitnessCodec.encode w) input w
    (by simp [scanStates]) (scan_closed enc) hdec
  have hws : ws = 1 := canonical_suffix w ws hcert
  subst ws
  refine ⟨is,hinput,?_⟩
  let x := Source284RawParse.payload input.bits
  let L := (is/4).bits
  let scratch := Source284DecodedScratch.tail limit 1
  let t := (Source284JoinedFrames.joinedBits x w).length+(seedCost enc+clock enc rest)
  have hzero : scratch = 0 := by simp [scratch,Source284DecodedScratch.tail]
  have hblank : Source284BitWindow.Agree (k+clock enc rest)
      (2*((2*scratch)/2^((Source284TaggedMarkerSeed.word enc).length+1))) 0 := by
    simp [hzero,Source284BitWindow.Agree]
  obtain ⟨rev',hs⟩ := Source284TaggedMarkerPipeline.scan_seed_serialize_strip
    enc x w rest L true scratch k hbody hblank
  have hleft : stack [true] (value L) = 2*(is/4)+1 := by
    simp [stack,L,Shared.Codes.BinaryAdditionCanonical.value_bits]
  rw [hleft] at hs
  have hr' : Source284Relative.run (description enc)
    (Source284Relative.initial (Source284TaggedWitnessCodec.encode w)
      (Source284UnaryPairScanner.pairTape (List.replicate limit false) input))
    (prefixCost limit input w+t) =
    Source284SourceRelocation.lift 782
      (Source284Relative.run (encode (scanStates enc) (scanTable enc) 1)
        ⟨2*(is/4)+1,stack (Source284JoinedFrames.joinedBits x w) scratch,active 0⟩ t) := by
    simpa [description,prefixCost,Source284DecodedScratch.tail,x,scratch,Nat.add_assoc] using hr t
  have hl := Source284SerializerStripWindow.lift_window k 782 _ _ hs
  change Window k (Source284SourceRelocation.lift 782
    (Source284Relative.run (encode (scanStates enc) (scanTable enc) 1)
      ⟨2*(is/4)+1,stack (Source284JoinedFrames.joinedBits x w) scratch,active 0⟩ t)) _ at hl
  rw [← hr'] at hl
  exact ⟨rev',hl⟩

end Shared.Beeping.NPcoNP.Source284CanonicalTaggedPipeline
