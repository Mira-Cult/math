import Shared.Beeping.NPcoNP.Source284ClearSerializer
import Shared.Beeping.NPcoNP.Source284SerializerStrip
import Shared.Beeping.NPcoNP.Source284SerializerStripWindow

/-! The clearing exit followed by the compiled frame-removal pass produces
the exact boundary shape expected by the reflected untagger. The program
starting the untagger is not yet linked to the frame control state. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284ClearStripSource

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramTaggedLoop (canonical result totalCost)
open Shared.Codes.FiniteProgramFrameLoop (framed words padding)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (compile codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284SerializerTrace (logical)
open Shared.Beeping.NPcoNP.Source284TableRun (toSource)
open Shared.Beeping.NPcoNP.Source284DetectorProduct (lifted)
open Shared.Beeping.NPcoNP.Source284DetectorExit (entry)

/-- A prepared serializer, its two-step clearing exit, and the actual frame
remover reach the reflected untagger's input shape. The output is a finite
window; arbitrary high input suffixes still need the separately proved window
adapter and a control link to the untagger. -/
theorem clear_then_strip {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (x w rest : List Bool) (dummy : Bool) (L : List Bool) (c : Config) (rev₀ : Bool)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest)
    (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical ((rest++[dummy])++L) false (Source284EncoderMarkerSeed.marker enc)).2)
    (k : Nat) :
    let zero := Source284EncoderFirstSelection.code enc false
    let one := Source284EncoderFirstSelection.code enc true
    let kept := Source284EncoderMarkerSeed.marker enc
    let remaining := rest++[dummy]
    let out := kept ++ (processed remaining false).flatMap (Source284EncoderFirstSelection.code enc)
    let N := totalCost zero one remaining false kept
    let frame := Shared.Codes.FiniteProgramFrameLoop.program width
    let frameRows := Source284FiniteRelativeRows.rows frame
    let states := (Source284DetectorProduct.serializerRows zero one).length
    let marks := Source284DetectorProduct.serializerMarks zero one
    let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
    let continuation := Source284ListTables.table frameRows
    let frameCost := Shared.Codes.FiniteProgramFrameLoop.totalCost width
      (Source284SerializerStrip.items enc remaining)
    let output := Source284Relative.run
      (Source284TableEncode.encode (entry states+frameRows.length)
        (Source284ClearExit.table states marks original continuation) 1)
      (toSource (lifted .lead (logical c.2 rev₀ 0))) (N+2+frameCost)
    ∃ rev, Window k output
      (Source284SourceRelocation.lift (entry states)
        (represented (tapeAt (cursor false (false::L.tail) out).2
          ((cursor false (false::L.tail) out).1::false::false::
            padding (processed remaining false).length [false,false]))
          rev (codeState (Shared.Codes.FiniteProgramFrameLoop.empty width) rev))) := by
  dsimp only
  let zero := Source284EncoderFirstSelection.code enc false
  let one := Source284EncoderFirstSelection.code enc true
  let kept := Source284EncoderMarkerSeed.marker enc
  let remaining := rest++[dummy]
  let bits := processed remaining false
  let items := bits.map (fun v => (v,Source284EncoderFirstSelection.code enc v))
  let frame := Shared.Codes.FiniteProgramFrameLoop.program width
  let frameRows := Source284FiniteRelativeRows.rows frame
  let states := (Source284DetectorProduct.serializerRows zero one).length
  let frameCost := Shared.Codes.FiniteProgramFrameLoop.totalCost width items
  let raw := (result zero one remaining false kept).2
  let t := Source284ClearTape.clearBoundary (canonical L (result zero one remaining false kept).1 raw).2
  let start := represented t false (codeState 0 false)
  have hn : 0 < frameRows.length := by simp [frameRows]
  have hc := Source284FiniteRelativeRows.closed frame (Shared.Codes.FiniteProgramFrameLoop.program_valid width)
  have he := Source284ClearSerializer.source_prepared_exit zero one frameRows.length
    (Source284ListTables.table frameRows) hn hc x w rest dummy kept L c rev₀ hbody hq ht frameCost
  rw [Source284FiniteRelativeRun.encode_eq_compile] at he
  have hwidth : ∀ item ∈ items, item.2.length = width := by
    intro item hi
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hi
    exact Source284TaggedCyclesSource.code_length enc v
  have hk : kept.length = width := Source284EncoderMarkerSeed.marker_length enc
  have hbuf : raw = kept++framed items :=
    Source284TaggedCyclesSource.encoder_result_framed enc remaining false
  have hw : Window (k+frameCost) start
      (represented (tapeAt (false::L.tail) (false::false::tagged (kept++framed items) ++
        false::[false,false])) false (codeState 0 false)) := by
    rw [← hbuf]
    change Window (k+frameCost) start start
    exact ⟨rfl,rfl,rfl⟩
  obtain ⟨rev,hframe⟩ := Source284FrameStripSource.frames_source_window width items hwidth
    kept (false::L.tail) [false,false] false false hk k start hw
  have hwords : words items = bits.flatMap (Source284EncoderFirstSelection.code enc) := by
    simp [words,items,List.flatMap_map]
  rw [hwords] at hframe
  have hl := Source284SerializerStripWindow.lift_window k (entry states) _ _ hframe
  rw [← he] at hl
  refine ⟨rev,?_⟩
  simpa [items,bits,frameCost,start,t,raw,zero,one,kept,remaining,states,frameRows,frame,
    Source284SerializerStrip.items,List.length_map] using hl

end Shared.Beeping.NPcoNP.Source284ClearStripSource
