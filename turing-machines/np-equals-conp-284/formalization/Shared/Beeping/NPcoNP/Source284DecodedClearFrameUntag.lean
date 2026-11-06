import Shared.Beeping.NPcoNP.Source284DecodedScratch
import Shared.Beeping.NPcoNP.Source284ClearFrameUntagPipeline
import Shared.Beeping.NPcoNP.Source284FrameUntagBudget

/-! The decoded certificate and raw input feed the fixed tagged serializer and reflected untagger.
This theorem uses only the zeros already present in the decoded scratch, so
it applies when its explicit size inequality holds. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284DecodedClearFrameUntag

open Shared.Codes.BitNumeralCompare (value)
open Shared.Codes.FiniteProgramTaggedLoop (canonical result totalCost)
open Shared.Codes.FiniteProgramFrameLoop (padding)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM2BinaryPostCosts (Alphabet)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284TableEncode (Row encode active)
open Shared.Beeping.NPcoNP.Source284TableRun (Closed)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284SerializerStrip (items)
open Shared.Beeping.NPcoNP.Source284DetectorExit (entry)
open Shared.Beeping.NPcoNP.Source284EncoderFirstSelection (code)
open Shared.Beeping.NPcoNP.Source284EncoderMarkerSeed (marker)

abbrev Codec (width : Nat) := Alphabet Source284JoinedRawEncodeTM2.machine → List.Vector Bool width

def serializerStates {width : Nat} (enc : Codec width) : Nat :=
  (Source284DetectorProduct.serializerRows (code enc false) (code enc true)).length

def frameRows (width : Nat) := Source284FiniteRelativeRows.rows (Shared.Codes.FiniteProgramFrameUntag.program width)

def continuationStates {width : Nat} (enc : Codec width) : Nat :=
  entry (serializerStates enc)+(frameRows width).length

def continuation {width : Nat} (enc : Codec width) : Nat → Bool → Row :=
  Source284ClearExit.table (serializerStates enc)
    (Source284DetectorProduct.serializerMarks (code enc false) (code enc true))
    (Source284ListTables.table (Source284DetectorProduct.serializerRows (code enc false) (code enc true)))
    (Source284ListTables.table (frameRows width))

def start : Nat := Nat.pair (Source284JoinedEndDetectorTable.index .lead)
  (Source284FiniteRelativeRows.index 0 true)

def scanTable {width : Nat} (enc : Codec width) : Nat → Bool → Row :=
  Source284JoinedPrefixScan.table
    (Source284TaggedMarkerSeed.table (Source284TaggedMarkerSeed.word enc) start (continuation enc))

def scanStates {width : Nat} (enc : Codec width) : Nat :=
  7+(1+(Source284HardwireTable.offset (Source284TaggedMarkerSeed.word enc)+(1+continuationStates enc)))

def seedCost {width : Nat} (enc : Codec width) : Nat :=
  1+Source284HardwireTable.offset (Source284TaggedMarkerSeed.word enc)+1

def clock {width : Nat} (enc : Codec width) (rest : List Bool) : Nat :=
  Source284FrameUntagBudget.clock enc (rest++[true])

def description {width : Nat} (enc : Codec width) : Nat :=
  Source284OffsetTagged.description
    (19+(80+(7+(210+(10+(160+(68+(16+scanStates enc))))))))
    (Source284BothFrames.table (Source284WitnessSeek.table
      (Source284WitnessCompact.table (Source284ScratchNormalize.table
        (Source284JoinedFrames.table (scanTable enc))))))

def prefixCost (limit input : Nat) (w : List Bool) : Nat :=
  Source284BothFrames.time limit w input+
    ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+
      (Source284WitnessCompact.extraCost (limit+1) w.length+((6*w.length+11)+
        (2*(Source284RawParse.payload input.bits).length+6))))

theorem continuation_closed {width : Nat} (enc : Codec width) :
    Closed (continuationStates enc) (continuation enc) := by
  apply Source284ClearExit.closed (serializerStates enc) (frameRows width).length _ _ _ (by simp [frameRows])
  · exact Source284FiniteRelativeRows.closed _ (Shared.Codes.FiniteProgramTaggedLoop.program_valid _ _)
  · exact Source284FiniteRelativeRows.closed _ (Shared.Codes.FiniteProgramFrameUntag.program_valid width)

theorem start_bound {width : Nat} (enc : Codec width) : start < continuationStates enc := by
  let program := Shared.Codes.FiniteProgramTaggedLoop.program (code enc false) (code enc true)
  have hp : 0 < program.length := Shared.Codes.FiniteProgramLink.valid_nonempty _
    (Shared.Codes.FiniteProgramTaggedLoop.program_valid _ _)
  let t := (canonical [] false []).2
  have hv := Source284SerializerTrace.logical_valid program t true 0 hp
  have hp' := Source284DetectorProduct.lifted_valid (serializerStates enc) .lead _ hv
  have h := hp' start (by rfl)
  dsimp [continuationStates,entry,Source284DetectorExit.entry]
  omega

theorem scan_closed {width : Nat} (enc : Codec width) : Closed (scanStates enc) (scanTable enc) := by
  apply Source284JoinedPrefixScan.closed _ _ (by simp [Source284HardwireTable.offset])
  exact Source284TaggedMarkerSeed.closed _ _ _ _ (start_bound enc) (continuation_closed enc)

/-- A valid decoded certificate reaches the frame-free, untagged output window if
the already-present scratch padding is long enough. The size inequality is
explicit and is not true by assumption for all inputs. -/
theorem decoded_to_raw_window {width : Nat} (enc : Codec width)
    (limit certificate input : Nat) (w rest : List Bool) (k : Nat)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w)
    (hbody : (Source284JoinedPrefixScan.joinedBody (Source284RawParse.payload input.bits) w).reverse = false::rest)
    (hsize : k+clock enc rest+(Source284TaggedMarkerSeed.word enc).length+1 ≤ 2*((limit+1)+1)) :
    ∃ witnessSuffix inputSuffix,
      certificate = 4*Source284Parser.encodeFrame w witnessSuffix ∧
      input = Source284Parser.encodeFrame (Source284RawParse.payload input.bits) inputSuffix ∧
      ∃ rev', Window k
        (Source284Relative.run (description enc)
          (Source284Relative.initial certificate
            (Source284UnaryPairScanner.pairTape (List.replicate limit false) input))
          (prefixCost limit input w+
            ((Source284JoinedFrames.joinedBits (Source284RawParse.payload input.bits) w).length+
              (seedCost enc+clock enc rest))))
        (let remaining := rest++[true]
         let L := (inputSuffix/4).bits
         let out := marker enc ++ (processed remaining false).flatMap (code enc)
         Source284SourceRelocation.lift 782
          (Source284SourceRelocation.lift (7+seedCost enc)
           (Source284SourceRelocation.lift (entry (serializerStates enc))
            (represented (tapeAt
              (false::false::Shared.Codes.FiniteProgramUntag.padding out.length (false::L.tail))
              (out++false::padding (processed remaining false).length [false,false]))
              rev' (codeState ((Shared.Codes.FiniteProgramFrameUntag.pre width).length+14) rev'))))) := by
  obtain ⟨ws,is,hcert,hinput,hr⟩ := Source284JoinedFrames.decoded_join_then
    (scanStates enc) (scanTable enc) limit certificate input w (by simp [scanStates])
    (scan_closed enc) hdec
  refine ⟨ws,is,hcert,hinput,?_⟩
  let x := Source284RawParse.payload input.bits
  let L := (is/4).bits
  let scratch := Source284DecodedScratch.tail limit ws
  let t := (Source284JoinedFrames.joinedBits x w).length+(seedCost enc+clock enc rest)
  have hblank := Source284DecodedScratch.decoded_zero_window limit ws (k+clock enc rest)
    ((Source284TaggedMarkerSeed.word enc).length+1) (by omega)
  obtain ⟨rev',hw⟩ := Source284ClearFrameUntagPipeline.scan_seed_serialize_strip
    enc x w rest L true scratch k hbody hblank
  have hleft : stack [true] (value L) = 2*(is/4)+1 := by
    simp [stack,L,Shared.Codes.BinaryAdditionCanonical.value_bits]
  rw [hleft] at hw
  have hr' : Source284Relative.run (description enc)
    (Source284Relative.initial certificate (Source284UnaryPairScanner.pairTape (List.replicate limit false) input))
    (prefixCost limit input w+t) =
    Source284SourceRelocation.lift 782
      (Source284Relative.run (encode (scanStates enc) (scanTable enc) 1)
        ⟨2*(is/4)+1,stack (Source284JoinedFrames.joinedBits x w) scratch,active 0⟩ t) := by
    simpa [description,prefixCost,Source284DecodedScratch.tail,x,scratch,Nat.add_assoc] using hr t
  have hl := Source284SerializerStripWindow.lift_window k 782 _ _ hw
  change Window k (Source284SourceRelocation.lift 782
    (Source284Relative.run (encode (scanStates enc) (scanTable enc) 1)
      ⟨2*(is/4)+1,stack (Source284JoinedFrames.joinedBits x w) scratch,active 0⟩ t)) _ at hl
  rw [← hr'] at hl
  exact ⟨rev',hl⟩

/-- Every old-cutoff witness accepted by the enlarged decoder reaches the
frame-free, untagged output window, even with arbitrary high certificate and input suffixes.
The enlarged unary limit is part of the input and is not generated for free. -/
theorem padded_decoded_to_raw_window {width : Nat} (enc : Codec width)
    (original certificate input : Nat) (w rest : List Bool) (k : Nat)
    (hdec : Source284TaggedWitnessCodec.decode
      (Source284FrameUntagBudget.paddedLimit width (Source284RawParse.payload input.bits).length original k) certificate = some w)
    (hw : w.length ≤ original)
    (hbody : (Source284JoinedPrefixScan.joinedBody (Source284RawParse.payload input.bits) w).reverse = false::rest) :
    let limit := Source284FrameUntagBudget.paddedLimit width (Source284RawParse.payload input.bits).length original k
    ∃ witnessSuffix inputSuffix,
      certificate = 4*Source284Parser.encodeFrame w witnessSuffix ∧
      input = Source284Parser.encodeFrame (Source284RawParse.payload input.bits) inputSuffix ∧
      ∃ rev', Window k
        (Source284Relative.run (description enc)
          (Source284Relative.initial certificate
            (Source284UnaryPairScanner.pairTape (List.replicate limit false) input))
          (prefixCost limit input w+
            ((Source284JoinedFrames.joinedBits (Source284RawParse.payload input.bits) w).length+
              (seedCost enc+clock enc rest))))
        (let remaining := rest++[true]
         let L := (inputSuffix/4).bits
         let out := marker enc ++ (processed remaining false).flatMap (code enc)
         Source284SourceRelocation.lift 782
          (Source284SourceRelocation.lift (7+seedCost enc)
           (Source284SourceRelocation.lift (entry (serializerStates enc))
            (represented (tapeAt
              (false::false::Shared.Codes.FiniteProgramUntag.padding out.length (false::L.tail))
              (out++false::padding (processed remaining false).length [false,false]))
              rev' (codeState ((Shared.Codes.FiniteProgramFrameUntag.pre width).length+14) rev'))))) := by
  apply decoded_to_raw_window enc _ certificate input w rest k hdec hbody
  exact Source284FrameUntagBudget.padding_sufficient enc _ w rest original k hbody hw


end Shared.Beeping.NPcoNP.Source284DecodedClearFrameUntag
