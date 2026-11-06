import Shared.Beeping.NPcoNP.Source284TaggedMarkerWindow

/-! Compose the actual joined-prefix scan and fixed tagged-marker writer
with the monitored serializer and finite frame stripping. The only scratch
hypothesis is an explicit finite low-zero window, not an all-blank tail. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284TaggedMarkerPipeline

open Shared.Codes.BitNumeralCompare (value)
open Shared.Codes.FiniteProgramTaggedLoop (canonical result totalCost)
open Shared.Codes.FiniteProgramFrameLoop (padding)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.Beeping.NPcoNP.Source284BitWindow (Agree)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284TableRun (Closed Valid toSource)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284SerializerStrip (items)
open Shared.Beeping.NPcoNP.Source284OrientedExit (entry)

/-- The pre-existing scan and the new fixed marker table feed the actual
monitored serializer and compiled metadata-removal program. The required
finite zero window in the untouched scratch suffix is the sole extra tape
hypothesis here; its dynamic construction remains to be proved. -/
theorem scan_seed_serialize_strip {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (x w rest L : List Bool) (dummy : Bool) (tail k : Nat)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest) :
    let zero := Source284EncoderFirstSelection.code enc false
    let one := Source284EncoderFirstSelection.code enc true
    let kept := Source284EncoderMarkerSeed.marker enc
    let word := Source284TaggedMarkerSeed.word enc
    let remaining := rest++[dummy]
    let b := (result zero one remaining false kept).1
    let out := kept ++ (processed remaining false).flatMap (Source284EncoderFirstSelection.code enc)
    let N := totalCost zero one remaining false kept
    let frame := Shared.Codes.FiniteProgramFrameLoop.program width
    let frameRows := Source284FiniteRelativeRows.rows frame
    let states := (Source284DetectorProduct.serializerRows zero one).length
    let marks := Source284DetectorProduct.serializerMarks zero one
    let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
    let continuation := Source284OrientedExit.table states marks original (Source284ListTables.table frameRows)
    let continuationStates := entry states+frameRows.length
    let start := Nat.pair (Source284JoinedEndDetectorTable.index .lead)
      (Source284FiniteRelativeRows.index 0 true)
    let frameCost := Shared.Codes.FiniteProgramFrameLoop.totalCost width (items enc remaining)
    let clock := N+2+frameCost
    let seedCost := 1+Source284HardwireTable.offset word+1
    let description := Source284TableEncode.encode
      (7+(1+(Source284HardwireTable.offset word+(1+continuationStates))))
      (Source284JoinedPrefixScan.table (Source284TaggedMarkerSeed.table word start continuation)) 1
    let input := ⟨stack [dummy] (value L),stack (Source284JoinedFrames.joinedBits x w) tail,
      Source284TableEncode.active 0⟩
    Agree (k+clock) (2*((2*tail)/2^(word.length+1))) 0 →
    ∃ rev', Window k
      (Source284Relative.run description input
        ((Source284JoinedFrames.joinedBits x w).length+(seedCost+clock)))
      (Source284SourceRelocation.lift (7+seedCost)
        (Source284SourceRelocation.lift (entry states)
          (represented (tapeAt (cursor b L out).2
            ((cursor b L out).1::false::false::padding (processed remaining false).length [false,false]))
            rev' (codeState (Shared.Codes.FiniteProgramFrameLoop.empty width) rev')))) := by
  dsimp only
  intro hblank
  let zero := Source284EncoderFirstSelection.code enc false
  let one := Source284EncoderFirstSelection.code enc true
  let kept := Source284EncoderMarkerSeed.marker enc
  let word := Source284TaggedMarkerSeed.word enc
  let remaining := rest++[dummy]
  let N := totalCost zero one remaining false kept
  let frame := Shared.Codes.FiniteProgramFrameLoop.program width
  let frameRows := Source284FiniteRelativeRows.rows frame
  let states := (Source284DetectorProduct.serializerRows zero one).length
  let marks := Source284DetectorProduct.serializerMarks zero one
  let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
  let cont := Source284OrientedExit.table states marks original (Source284ListTables.table frameRows)
  let contStates := entry states+frameRows.length
  let start := Nat.pair (Source284JoinedEndDetectorTable.index .lead)
    (Source284FiniteRelativeRows.index 0 true)
  let frameCost := Shared.Codes.FiniteProgramFrameLoop.totalCost width (items enc remaining)
  let clock := N+2+frameCost
  let seedCost := 1+Source284HardwireTable.offset word+1
  let actual : Source284Relative.Config :=
    ⟨stack word (2*((2*tail)/2^(word.length+1))),
      stack (false::rest) (stack [dummy] (value L)),Source284TableEncode.active start⟩
  have hpos : 0 < (Shared.Codes.FiniteProgramTaggedLoop.program zero one).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one)
  have hlogical := Source284SerializerTrace.logical_valid
    (Shared.Codes.FiniteProgramTaggedLoop.program zero one)
    (canonical (remaining++L) false kept).2 true 0 hpos
  have hlift := Source284DetectorProduct.lifted_valid states .lead _ hlogical
  have hstart : start < contStates := by
    have h := hlift start (by rfl)
    dsimp [contStates,entry,Source284OrientedExit.entry]
    omega
  have hclosed : Closed contStates cont := by
    apply Source284OrientedExit.closed states frameRows.length marks original _ (by simp [frameRows])
    · exact Source284FiniteRelativeRows.closed _ (Shared.Codes.FiniteProgramTaggedLoop.program_valid zero one)
    · exact Source284FiniteRelativeRows.closed frame (Shared.Codes.FiniteProgramFrameLoop.program_valid width)
  have hr := Source284TaggedMarkerSeed.source_scan_then x w word contStates start cont
    (stack [dummy] (value L)) tail clock hstart hclosed
  rw [hbody] at hr
  have hw := Source284TaggedMarkerWindow.seeded_window enc rest L dummy (2*tail) (k+clock) hblank
  change Window (k+clock) actual _ at hw
  obtain ⟨rev',hs⟩ := Source284SerializerStripWindow.serializer_then_strip_window
    enc x w rest dummy L true hbody k actual hw
  have hl := Source284SerializerStripWindow.lift_window k (7+seedCost) _ _ hs
  change Window k (Source284SourceRelocation.lift (7+seedCost)
    (Source284Relative.run (Source284TableEncode.encode contStates cont 1) actual clock)) _ at hl
  rw [← hr] at hl
  exact ⟨rev',hl⟩

end Shared.Beeping.NPcoNP.Source284TaggedMarkerPipeline
