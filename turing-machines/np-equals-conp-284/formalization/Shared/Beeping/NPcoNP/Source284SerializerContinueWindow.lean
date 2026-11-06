import Shared.Beeping.NPcoNP.Source284SerializerContinue

/-! Finite-window robustness of the fixed serializer/continuation table.
The continuation's own run and the initial window are explicit premises. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284SerializerContinueWindow

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTaggedLoop (canonical totalCost)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284SerializerTrace (logical)
open Shared.Beeping.NPcoNP.Source284TableRun (toSource)
open Shared.Beeping.NPcoNP.Source284DetectorProduct (lifted)
open Shared.Beeping.NPcoNP.Source284DetectorExit (entry)

/-- Arbitrary higher source tape cells do not affect a requested output
window when the initial window covers every paid serializer and continuation
step. No global blank-tape premise is made. -/
theorem serializer_continue_window {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (x w rest : List Bool) (dummy : Bool) (L : List Bool) (rev₀ : Bool)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest)
    (next : Program) (hn : valid next = true) (fuel : Nat) (last : Config)
    (hnext : let out := Source284EncoderMarkerSeed.marker enc ++
        (processed (rest++[dummy]) false).flatMap (Source284EncoderFirstSelection.code enc)
      run next (0,Source284UntagOutputWindow.outputTape out L.tail
        (processed (rest++[dummy]) false).length) fuel = some (.inr last))
    (k : Nat) (actual : Source284Relative.Config) :
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
    let clock := N+2+cost
    let description := Source284TableEncode.encode (entry states+rows.length)
      (Source284ClearExit.table states marks original (Source284ListTables.table rows)) 1
    let reference := toSource (lifted .lead
      (logical (canonical (remaining++L) false kept).2 rev₀ 0))
    Window (k+clock) actual reference →
    ∃ rev, Window k (Source284Relative.run description actual clock)
      (Source284SourceRelocation.lift (entry states)
        (represented last.2 rev (codeState
          ((Shared.Codes.FiniteProgramFrameUntag.program width).length+2+last.1) rev))) := by
  dsimp only
  intro hw
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
  let clock := N+2+cost
  let description := Source284TableEncode.encode (entry states+rows.length)
    (Source284ClearExit.table states marks original (Source284ListTables.table rows)) 1
  let input := canonical (remaining++L) false kept
  let reference := toSource (lifted .lead (logical input.2 rev₀ 0))
  have ht : Shared.Codes.FiniteProgramTapeEquiv.TapeRel input.2
      (canonical ((rest++[dummy])++L) false kept).2 := by rfl
  obtain ⟨rev,htarget⟩ := Source284SerializerContinue.serializer_then_continuation
    enc x w rest dummy L input rev₀ hbody rfl ht next hn fuel last hnext k
  have hr : Window k (Source284Relative.run description actual clock)
      (Source284Relative.run description reference clock) :=
    Source284Relative.run_window description clock k actual reference hw
  exact ⟨rev,Source284SerializerStripWindow.window_trans k _ _ _ hr htarget⟩

end Shared.Beeping.NPcoNP.Source284SerializerContinueWindow
