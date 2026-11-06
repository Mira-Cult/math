import Shared.Beeping.NPcoNP.Source284ClearStripSource
import Shared.Codes.FiniteProgramFrameUntag

/-! The cleared serializer now feeds one finite frame-removal/untagging
program. Initial tagged buffers and later encoder control remain explicit. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284ClearFrameUntag

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramTaggedLoop (canonical result totalCost)
open Shared.Codes.FiniteProgramFrameLoop (framed words padding)
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

/-- The prepared serializer clears its boundary, removes frame metadata,
pays the two-step frame-to-untagger link, and produces raw serialized words.
The resulting source window still carries explicit high tape suffixes. -/
theorem clear_frame_untag {width : Nat}
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
    let program := Shared.Codes.FiniteProgramFrameUntag.program width
    let rows := Source284FiniteRelativeRows.rows program
    let states := (Source284DetectorProduct.serializerRows zero one).length
    let marks := Source284DetectorProduct.serializerMarks zero one
    let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
    let items := Source284SerializerStrip.items enc remaining
    let cost := Shared.Codes.FiniteProgramFrameLoop.totalCost width items+2+
      (2+Shared.Codes.FiniteProgramUntag.cost out.reverse)
    let output := Source284Relative.run
      (Source284TableEncode.encode (entry states+rows.length)
        (Source284ClearExit.table states marks original (Source284ListTables.table rows)) 1)
      (toSource (lifted .lead (logical c.2 rev₀ 0))) (N+2+cost)
    ∃ rev, Window k output
      (Source284SourceRelocation.lift (entry states)
        (represented (tapeAt
          (false::false::Shared.Codes.FiniteProgramUntag.padding out.length (false::L.tail))
          (out++false::padding (processed remaining false).length [false,false]))
          rev (codeState ((Shared.Codes.FiniteProgramFrameUntag.pre width).length+14) rev))) := by
  dsimp only
  let zero := Source284EncoderFirstSelection.code enc false
  let one := Source284EncoderFirstSelection.code enc true
  let kept := Source284EncoderMarkerSeed.marker enc
  let remaining := rest++[dummy]
  let bits := processed remaining false
  let items := bits.map (fun v => (v,Source284EncoderFirstSelection.code enc v))
  let out := kept++bits.flatMap (Source284EncoderFirstSelection.code enc)
  let program := Shared.Codes.FiniteProgramFrameUntag.program width
  let rows := Source284FiniteRelativeRows.rows program
  let states := (Source284DetectorProduct.serializerRows zero one).length
  let cost := Shared.Codes.FiniteProgramFrameLoop.totalCost width items+2+
    (2+Shared.Codes.FiniteProgramUntag.cost out.reverse)
  let raw := (result zero one remaining false kept).2
  let t := Source284ClearTape.clearBoundary (canonical L (result zero one remaining false kept).1 raw).2
  let start := represented t false (codeState 0 false)
  have hn : 0 < rows.length := by simp [rows]
  have hc := Source284FiniteRelativeRows.closed program (Shared.Codes.FiniteProgramFrameUntag.program_valid width)
  have he := Source284ClearSerializer.source_prepared_exit zero one rows.length
    (Source284ListTables.table rows) hn hc x w rest dummy kept L c rev₀ hbody hq ht cost
  rw [Source284FiniteRelativeRun.encode_eq_compile] at he
  have hwidth : ∀ item ∈ items, item.2.length = width := by
    intro item hi
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hi
    exact Source284TaggedCyclesSource.code_length enc v
  have hk : kept.length = width := Source284EncoderMarkerSeed.marker_length enc
  have hbuf : raw = kept++framed items :=
    Source284TaggedCyclesSource.encoder_result_framed enc remaining false
  have hwords : words items = bits.flatMap (Source284EncoderFirstSelection.code enc) := by
    simp [words,items,List.flatMap_map]
  let initial := tapeAt (false::L.tail) (false::false::tagged (kept++framed items) ++ false::[false,false])
  let final := tapeAt (false::false::Shared.Codes.FiniteProgramUntag.padding out.length (false::L.tail))
    (out++false::padding items.length [false,false])
  have hrun := Shared.Codes.FiniteProgramFrameUntag.frame_then_untag width items hwidth kept L.tail [false,false] hk
  rw [hwords] at hrun
  change run program (0,initial) cost = some (.inr ((Shared.Codes.FiniteProgramFrameUntag.pre width).length+14,final)) at hrun
  have hw : Window (k+cost) start (represented initial false (codeState 0 false)) := by
    dsimp [initial]
    rw [← hbuf]
    change Window (k+cost) start start
    exact ⟨rfl,rfl,rfl⟩
  have hp : 0 < program.length := Shared.Codes.FiniteProgramLink.valid_nonempty program
    (Shared.Codes.FiniteProgramFrameUntag.program_valid width)
  obtain ⟨rev,hfinal⟩ := Source284FrameStripSource.compiled_tape_window program 0
    ((Shared.Codes.FiniteProgramFrameUntag.pre width).length+14) initial final false cost k start
    (Shared.Codes.FiniteProgramFrameUntag.program_valid width) hp hrun hw
  have hl := Source284SerializerStripWindow.lift_window k (entry states) _ _ hfinal
  rw [← he] at hl
  refine ⟨rev,?_⟩
  simpa [items,bits,cost,start,t,raw,zero,one,kept,remaining,states,rows,program,final,out,
    Source284SerializerStrip.items,List.length_map] using hl

end Shared.Beeping.NPcoNP.Source284ClearFrameUntag
