import Shared.Beeping.NPcoNP.Source284OrientedSerializer
import Shared.Beeping.NPcoNP.Source284FrameStripSource

/-! The detector's orientation-preserving exit hands the prepared serializer's
actual tagged buffer to the compiled finite frame-removal pass. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284SerializerStrip

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramTaggedLoop (canonical result totalCost)
open Shared.Codes.FiniteProgramFrameLoop (padding)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (compile codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284SerializerTrace (logical)
open Shared.Beeping.NPcoNP.Source284TableRun (toSource)
open Shared.Beeping.NPcoNP.Source284DetectorProduct (lifted)
open Shared.Beeping.NPcoNP.Source284OrientedExit (entry table)

def items {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (remaining : List Bool) : List (Bool × List Bool) :=
  (processed remaining false).map (fun v => (v,Source284EncoderFirstSelection.code enc v))

/-- Given the exact tagged buffer, the compiled frame-removal phase has the
advertised output window for any requested finite radius. -/
theorem strip_from_canonical {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (remaining L : List Bool) (rev₀ : Bool) (k : Nat) :
    let zero := Source284EncoderFirstSelection.code enc false
    let one := Source284EncoderFirstSelection.code enc true
    let kept := Source284EncoderMarkerSeed.marker enc
    let b := (result zero one remaining false kept).1
    let out := kept ++ (processed remaining false).flatMap (Source284EncoderFirstSelection.code enc)
    let start := represented (canonical L b (result zero one remaining false kept).2).2 rev₀ (codeState 0 rev₀)
    ∃ rev, Window k
      (Source284Relative.run (compile (Shared.Codes.FiniteProgramFrameLoop.program width)) start
        (Shared.Codes.FiniteProgramFrameLoop.totalCost width (items enc remaining)))
      (represented (tapeAt (cursor b L out).2
        ((cursor b L out).1::false::false::padding (processed remaining false).length [false,false]))
        rev (codeState (Shared.Codes.FiniteProgramFrameLoop.empty width) rev)) := by
  dsimp only
  let zero := Source284EncoderFirstSelection.code enc false
  let one := Source284EncoderFirstSelection.code enc true
  let kept := Source284EncoderMarkerSeed.marker enc
  let b := (result zero one remaining false kept).1
  let start := represented (canonical L b (result zero one remaining false kept).2).2 rev₀ (codeState 0 rev₀)
  have hw : Window (k+Shared.Codes.FiniteProgramFrameLoop.totalCost width (items enc remaining)) start start :=
    ⟨rfl,rfl,rfl⟩
  have hw' := hw
  change Window (k+Shared.Codes.FiniteProgramFrameLoop.totalCost width (items enc remaining)) start
    (represented (tapeAt L (b::false::Shared.Codes.FiniteProgramBitShuttle.tagged
      (result zero one remaining false kept).2 ++ false::[false,false])) rev₀ (codeState 0 rev₀)) at hw'
  have h := Source284FrameStripSource.encoder_frames_source_window enc remaining false L [false,false] rev₀ k start hw'
  simpa [items,zero,one,kept,b,start] using h

/-- A prepared detector/serializer run continues, after two paid orientation
bridge steps, through the actual compiled finite frame-removal program.
The resulting finite output window has no metadata bits. -/
theorem serializer_then_strip {width : Nat}
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
    let b := (result zero one remaining false kept).1
    let out := kept ++ (processed remaining false).flatMap (Source284EncoderFirstSelection.code enc)
    let N := totalCost zero one remaining false kept
    let frame := Shared.Codes.FiniteProgramFrameLoop.program width
    let frameRows := Source284FiniteRelativeRows.rows frame
    let states := (Source284DetectorProduct.serializerRows zero one).length
    let marks := Source284DetectorProduct.serializerMarks zero one
    let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
    let continuation := Source284ListTables.table frameRows
    let frameCost := Shared.Codes.FiniteProgramFrameLoop.totalCost width (items enc remaining)
    let output := Source284Relative.run
      (Source284TableEncode.encode (entry states+frameRows.length)
        (table states marks original continuation) 1)
      (toSource (lifted .lead (logical c.2 rev₀ 0))) (N+2+frameCost)
    ∃ rev rev',
      output = Source284SourceRelocation.lift (entry states)
        (Source284Relative.run (compile frame)
          (represented (canonical L b (result zero one remaining false kept).2).2 rev (codeState 0 rev)) frameCost) ∧
      Window k (Source284Relative.run (compile frame)
          (represented (canonical L b (result zero one remaining false kept).2).2 rev (codeState 0 rev)) frameCost)
        (represented (tapeAt (cursor b L out).2
          ((cursor b L out).1::false::false::padding (processed remaining false).length [false,false]))
          rev' (codeState (Shared.Codes.FiniteProgramFrameLoop.empty width) rev')) := by
  dsimp only
  let zero := Source284EncoderFirstSelection.code enc false
  let one := Source284EncoderFirstSelection.code enc true
  let kept := Source284EncoderMarkerSeed.marker enc
  let remaining := rest++[dummy]
  let frame := Shared.Codes.FiniteProgramFrameLoop.program width
  let frameRows := Source284FiniteRelativeRows.rows frame
  let frameCost := Shared.Codes.FiniteProgramFrameLoop.totalCost width (items enc remaining)
  have hn : 2 ≤ frameRows.length := by simp [frameRows]
  have hc := Source284FiniteRelativeRows.closed frame (Shared.Codes.FiniteProgramFrameLoop.program_valid width)
  obtain ⟨rev,he⟩ := Source284OrientedSerializer.serializer_exit_prepared zero one frameRows.length
    (Source284ListTables.table frameRows) hn hc x w rest dummy kept L c rev₀ hbody hq ht frameCost
  rw [Source284FiniteRelativeRun.encode_eq_compile] at he
  obtain ⟨rev',hw⟩ := strip_from_canonical enc remaining L rev k
  exact ⟨rev,rev',he,hw⟩

end Shared.Beeping.NPcoNP.Source284SerializerStrip
