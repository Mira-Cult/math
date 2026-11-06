import Shared.Beeping.NPcoNP.Source284ClearFrameUntag
import Shared.Beeping.NPcoNP.Source284UntagOutputWindow
import Shared.Codes.FiniteProgramFrameUntagContinue

/-! A prepared marked serializer and an explicitly spliced finite continuation
share one numeric source table. The supplied continuation run is a hypothesis;
workspace provisioning and physical-table refinement are separate obligations. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284SerializerContinue

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramTaggedLoop (canonical result totalCost)
open Shared.Codes.FiniteProgramFrameLoop (framed words padding)
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284SerializerTrace (logical)
open Shared.Beeping.NPcoNP.Source284TableRun (toSource)
open Shared.Beeping.NPcoNP.Source284DetectorProduct (lifted)
open Shared.Beeping.NPcoNP.Source284DetectorExit (entry)

/-- Starting on a prepared tagged tape, the marked serializer, clearing exit,
frame pass, untagger, splice, and continuation execute in one fixed source
table. The continuation run explicitly starts from the actual raw output tape,
including its retained high suffix. -/
theorem serializer_then_continuation {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (x w rest : List Bool) (dummy : Bool) (L : List Bool) (c : Config) (rev₀ : Bool)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest)
    (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical ((rest++[dummy])++L) false (Source284EncoderMarkerSeed.marker enc)).2)
    (next : Program) (hn : valid next = true) (fuel : Nat) (last : Config)
    (hnext : let out := Source284EncoderMarkerSeed.marker enc ++
        (processed (rest++[dummy]) false).flatMap (Source284EncoderFirstSelection.code enc)
      run next (0,Source284UntagOutputWindow.outputTape out L.tail
        (processed (rest++[dummy]) false).length) fuel = some (.inr last))
    (k : Nat) :
    let zero := Source284EncoderFirstSelection.code enc false
    let one := Source284EncoderFirstSelection.code enc true
    let kept := Source284EncoderMarkerSeed.marker enc
    let remaining := rest++[dummy]
    let out := kept ++ (processed remaining false).flatMap (Source284EncoderFirstSelection.code enc)
    let N := totalCost zero one remaining false kept
    let program := Shared.Codes.FiniteProgramFrameUntagContinue.program width next
    let rows := Source284FiniteRelativeRows.rows program
    let states := (Source284DetectorProduct.serializerRows zero one).length
    let marks := Source284DetectorProduct.serializerMarks zero one
    let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
    let items := Source284SerializerStrip.items enc remaining
    let cost := Shared.Codes.FiniteProgramFrameLoop.totalCost width items+2+
      (2+Shared.Codes.FiniteProgramUntag.cost out.reverse)+2+fuel
    let output := Source284Relative.run
      (Source284TableEncode.encode (entry states+rows.length)
        (Source284ClearExit.table states marks original (Source284ListTables.table rows)) 1)
      (toSource (lifted .lead (logical c.2 rev₀ 0))) (N+2+cost)
    ∃ rev, Window k output
      (Source284SourceRelocation.lift (entry states)
        (represented last.2 rev (codeState
          ((Shared.Codes.FiniteProgramFrameUntag.program width).length+2+last.1) rev))) := by
  dsimp only
  let zero := Source284EncoderFirstSelection.code enc false
  let one := Source284EncoderFirstSelection.code enc true
  let kept := Source284EncoderMarkerSeed.marker enc
  let remaining := rest++[dummy]
  let bits := processed remaining false
  let items := bits.map (fun v => (v,Source284EncoderFirstSelection.code enc v))
  let out := kept++bits.flatMap (Source284EncoderFirstSelection.code enc)
  let program := Shared.Codes.FiniteProgramFrameUntagContinue.program width next
  let rows := Source284FiniteRelativeRows.rows program
  let states := (Source284DetectorProduct.serializerRows zero one).length
  let cost := Shared.Codes.FiniteProgramFrameLoop.totalCost width items+2+
    (2+Shared.Codes.FiniteProgramUntag.cost out.reverse)+2+fuel
  let raw := (result zero one remaining false kept).2
  let t := Source284ClearTape.clearBoundary (canonical L (result zero one remaining false kept).1 raw).2
  let start := represented t false (codeState 0 false)
  have hpvalid := Shared.Codes.FiniteProgramFrameUntagContinue.program_valid width next hn
  have hc := Source284FiniteRelativeRows.closed program hpvalid
  have he := Source284ClearSerializer.source_prepared_exit zero one rows.length
    (Source284ListTables.table rows) (by simp [rows]) hc x w rest dummy kept L c rev₀ hbody hq ht cost
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
  have hnext' : run next (0,tapeAt
      (false::false::Shared.Codes.FiniteProgramUntag.padding out.length (false::L.tail))
      (out++false::padding items.length [false,false])) fuel = some (.inr last) := by
    simpa [Source284UntagOutputWindow.outputTape,items,bits,out,remaining,kept,List.length_map] using hnext
  have heout : kept++words items = out := by simp [out,hwords]
  rw [← heout] at hnext'
  have hrun := Shared.Codes.FiniteProgramFrameUntagContinue.frame_untag_then
    width items hwidth kept L.tail hk next hn fuel last hnext'
  rw [hwords] at hrun
  change run program (0,initial) cost = some (.inr
    (((Shared.Codes.FiniteProgramFrameUntag.program width).length+2+last.1),last.2)) at hrun
  have hw : Window (k+cost) start (represented initial false (codeState 0 false)) := by
    dsimp [initial]
    rw [← hbuf]
    change Window (k+cost) start start
    exact ⟨rfl,rfl,rfl⟩
  have hp : 0 < program.length := Shared.Codes.FiniteProgramLink.valid_nonempty program hpvalid
  obtain ⟨rev,hfinal⟩ := Source284FrameStripSource.compiled_tape_window program 0
    ((Shared.Codes.FiniteProgramFrameUntag.program width).length+2+last.1) initial last.2 false cost k start
    hpvalid hp hrun hw
  have hl := Source284SerializerStripWindow.lift_window k (entry states) _ _ hfinal
  rw [← he] at hl
  refine ⟨rev,?_⟩
  simpa [items,bits,cost,start,t,raw,zero,one,kept,remaining,states,rows,program,out,
    Source284SerializerStrip.items,List.length_map] using hl

end Shared.Beeping.NPcoNP.Source284SerializerContinue
