import Shared.Beeping.NPcoNP.Source284FiniteLiveWindow
import Shared.Beeping.NPcoNP.Source284SerializerContinueWindow
import Shared.Beeping.NPcoNP.Source284ClearedUntagSource

/-! Discharge the serializer continuation premise from an independently
proved live encoder run, when its finite window fits the actual zero runway. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284SerializerEncoderRun

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTaggedLoop (canonical totalCost)
open Shared.ComplexityBridge.TM2BinaryPostCosts (inputBits)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284SerializerTrace (logical)
open Shared.Beeping.NPcoNP.Source284TableRun (toSource)
open Shared.Beeping.NPcoNP.Source284DetectorProduct (lifted)
open Shared.Beeping.NPcoNP.Source284DetectorExit (entry)

/-- A live reference run on the canonical serialized joined input yields a
live run on the untagger's actual output, at the same clock and control.
Only the stated finite runway is required; the retained suffix is arbitrary. -/
theorem joined_output_live {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (x w rest : List Bool) (dummy : Bool) (suffix : List Bool)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest)
    (next : Program) (hn : valid next = true) (fuel k q : Nat) (reference : Tape)
    (hrun : run next (initial (inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w))) fuel = some (.inr (q,reference)))
    (hsize : k+fuel ≤ 2*(inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w)).length+3) :
    let out := Source284EncoderMarkerSeed.marker enc ++
      (processed (rest++[dummy]) false).flatMap (Source284EncoderFirstSelection.code enc)
    ∃ actual rev,
      run next (0,Source284UntagOutputWindow.outputTape out suffix
        (processed (rest++[dummy]) false).length) fuel = some (.inr (q,actual)) ∧
      Window k (represented actual rev (codeState q rev))
        (represented reference rev (codeState q rev)) := by
  dsimp only
  let out := Source284EncoderMarkerSeed.marker enc ++
    (processed (rest++[dummy]) false).flatMap (Source284EncoderFirstSelection.code enc)
  have hwords : out = inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w) :=
    Source284ClearedUntagSource.serialized_words enc x w rest dummy hbody
  have hsize' : k+fuel ≤ 2*out.length+3 := by rw [hwords]; exact hsize
  have hw := Source284UntagOutputWindow.output_window out suffix
    (processed (rest++[dummy]) false).length (k+fuel) hsize'
  change Window (k+fuel)
    (represented (Source284UntagOutputWindow.outputTape out suffix
      (processed (rest++[dummy]) false).length) false (codeState 0 false)) _ at hw
  have hr : run next (initial out) fuel = some (.inr (q,reference)) := by
    rw [hwords]
    exact hrun
  exact Source284FiniteLiveWindow.live_run_of_window next out _ fuel k q reference hn hr hw

/-- The finite source table now actually runs the serializer and encoder,
provided the reference encoder prefix fits the proved output runway and the
starting source window covers the whole charged execution. -/
theorem serializer_runs_joined_prefix {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (x w rest : List Bool) (dummy : Bool) (L : List Bool) (rev₀ : Bool)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest)
    (next : Program) (hn : valid next = true) (fuel kEncoder kSource q : Nat) (reference : Tape)
    (hrun : run next (initial (inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w))) fuel = some (.inr (q,reference)))
    (hsize : kEncoder+fuel ≤ 2*(inputBits Source284JoinedRawEncodeTM2.machine enc
      (Source284JoinedFrames.joinedBits x w)).length+3)
    (actual : Source284Relative.Config) :
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
    let initialRef := toSource (lifted .lead
      (logical (canonical (remaining++L) false kept).2 rev₀ 0))
    Window (kSource+clock) actual initialRef →
    ∃ actualTape rev revSource,
      Window kEncoder (represented actualTape rev (codeState q rev))
        (represented reference rev (codeState q rev)) ∧
      Window kSource (Source284Relative.run description actual clock)
        (Source284SourceRelocation.lift (entry states)
          (represented actualTape revSource (codeState
            ((Shared.Codes.FiniteProgramFrameUntag.program width).length+2+q) revSource))) := by
  dsimp only
  intro hw
  obtain ⟨actualTape,rev,hr,henc⟩ := joined_output_live enc x w rest dummy L.tail
    hbody next hn fuel kEncoder q reference hrun hsize
  obtain ⟨revSource,hsource⟩ := Source284SerializerContinueWindow.serializer_continue_window
    enc x w rest dummy L rev₀ hbody next hn fuel (q,actualTape) hr kSource actual hw
  exact ⟨actualTape,rev,revSource,henc,hsource⟩

end Shared.Beeping.NPcoNP.Source284SerializerEncoderRun
