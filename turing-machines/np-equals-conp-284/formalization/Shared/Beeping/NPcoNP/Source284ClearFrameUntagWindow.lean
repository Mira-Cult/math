import Shared.Beeping.NPcoNP.Source284ClearFrameUntag

/-! Finite-window robustness for the clearing, frame-removal and untagging
pipeline. Arbitrary higher source tape cells are allowed. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284ClearFrameUntagWindow

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTaggedLoop (canonical totalCost)
open Shared.Codes.FiniteProgramFrameLoop (padding)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284SerializerTrace (logical)
open Shared.Beeping.NPcoNP.Source284TableRun (toSource)
open Shared.Beeping.NPcoNP.Source284DetectorProduct (lifted)
open Shared.Beeping.NPcoNP.Source284DetectorExit (entry)

/-- A source tape needs only `k + clock` agreement with the prepared tape;
all higher data may differ. The clock includes clearing and untagging. -/
theorem clear_frame_untag_window {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (x w rest : List Bool) (dummy : Bool) (L : List Bool) (rev₀ : Bool)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest)
    (k : Nat) (actual : Source284Relative.Config) :
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
    let clock := N+2+cost
    let description := Source284TableEncode.encode (entry states+rows.length)
      (Source284ClearExit.table states marks original (Source284ListTables.table rows)) 1
    let reference := toSource (lifted .lead
      (logical (canonical (remaining++L) false kept).2 rev₀ 0))
    Window (k+clock) actual reference →
    ∃ rev, Window k (Source284Relative.run description actual clock)
      (Source284SourceRelocation.lift (entry states)
        (represented (tapeAt
          (false::false::Shared.Codes.FiniteProgramUntag.padding out.length (false::L.tail))
          (out++false::padding (processed remaining false).length [false,false]))
          rev (codeState ((Shared.Codes.FiniteProgramFrameUntag.pre width).length+14) rev))) := by
  dsimp only
  intro hw
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
  let clock := N+2+cost
  let description := Source284TableEncode.encode (entry states+rows.length)
    (Source284ClearExit.table states marks original (Source284ListTables.table rows)) 1
  let input := canonical (remaining++L) false kept
  let reference := toSource (lifted .lead (logical input.2 rev₀ 0))
  have ht : Shared.Codes.FiniteProgramTapeEquiv.TapeRel input.2
      (canonical ((rest++[dummy])++L) false kept).2 := by rfl
  obtain ⟨rev,htarget⟩ := Source284ClearFrameUntag.clear_frame_untag
    enc x w rest dummy L input rev₀ hbody rfl ht k
  have hr : Window k (Source284Relative.run description actual clock)
      (Source284Relative.run description reference clock) :=
    Source284Relative.run_window description clock k actual reference hw
  exact ⟨rev,Source284SerializerStripWindow.window_trans k _ _ _ hr htarget⟩

end Shared.Beeping.NPcoNP.Source284ClearFrameUntagWindow
