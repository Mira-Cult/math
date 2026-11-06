import Shared.Beeping.NPcoNP.Source284SerializerStrip

/-! Finite-window version of the prepared serializer/strip handoff. High tape
cells are arbitrary; the window size explicitly pays for every source step. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284SerializerStripWindow

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTaggedLoop (canonical result totalCost)
open Shared.Codes.FiniteProgramFrameLoop (padding)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284SerializerTrace (logical)
open Shared.Beeping.NPcoNP.Source284TableRun (toSource)
open Shared.Beeping.NPcoNP.Source284DetectorProduct (lifted)
open Shared.Beeping.NPcoNP.Source284OrientedExit (entry table)
open Shared.Beeping.NPcoNP.Source284SerializerStrip (items)

/-- Equal low-cell windows compose, including the source control state. -/
theorem window_trans (k : Nat) (a b c : Source284Relative.Config)
    (hab : Window k a b) (hbc : Window k b c) : Window k a c := by
  exact ⟨hab.1.trans hbc.1,hab.2.1.trans hbc.2.1,hab.2.2.trans hbc.2.2⟩

/-- Relocating both controls preserves their finite-window agreement. -/
theorem lift_window (k d : Nat) (a b : Source284Relative.Config)
    (h : Window k a b) : Window k (Source284SourceRelocation.lift d a)
      (Source284SourceRelocation.lift d b) := by
  rcases h with ⟨hs,hl,hr⟩
  refine ⟨?_,hl,hr⟩
  simp only [Source284SourceRelocation.lift]
  rw [hs]

theorem processed_length (remaining : List Bool) (b : Bool) :
    (processed remaining b).length = remaining.length := by
  induction remaining generalizing b with
  | nil => rfl
  | cons p ps ih => simp [processed,ih]

/-- An explicit polynomial upper bound on the complete serializer, two-step
exit, and frame-removal runtime, in the input-bit count and codec width. -/
theorem combined_cost_bound {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (remaining : List Bool) :
    let m := remaining.length
    totalCost (Source284EncoderFirstSelection.code enc false)
      (Source284EncoderFirstSelection.code enc true) remaining false
      (Source284EncoderMarkerSeed.marker enc) + 2 +
      Shared.Codes.FiniteProgramFrameLoop.totalCost width (items enc remaining) ≤
      m*(16*(width+m*(1+width))+16*width+31) + 2 +
        (m+1)*(7*width+30*((m+1)*(width+1))+26) := by
  dsimp only
  have hs := Shared.Codes.FiniteProgramTaggedLoop.totalCost_bound
    (Source284EncoderFirstSelection.code enc false)
    (Source284EncoderFirstSelection.code enc true) remaining false
    (Source284EncoderMarkerSeed.marker enc)
  rw [Source284EncoderMarkerSeed.marker_length,Source284TaggedCyclesSource.maxWord_encoder] at hs
  have hwidth : ∀ item ∈ items enc remaining, item.2.length = width := by
    intro item hi
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hi
    exact Source284TaggedCyclesSource.code_length enc v
  have hf := Shared.Codes.FiniteProgramFrameLoop.totalCost_bound width (items enc remaining) hwidth
  have hi : (items enc remaining).length = remaining.length := by simp [items,processed_length]
  rw [hi] at hf
  omega

/-- The full serializer and actual metadata-removal table work from an
arbitrary source configuration that agrees with the prepared tape only in
`k + runtime` cells on each half. No condition is imposed on higher cells.
The output agrees in its requested `k` cells with the metadata-free result,
up to the explicitly reported final orientation. -/
theorem serializer_then_strip_window {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (x w rest : List Bool) (dummy : Bool) (L : List Bool) (rev₀ : Bool)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest)
    (k : Nat) (actual : Source284Relative.Config) :
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
    let clock := N+2+frameCost
    let description := Source284TableEncode.encode (entry states+frameRows.length)
      (table states marks original continuation) 1
    let reference := toSource (lifted .lead
      (logical (canonical (remaining++L) false kept).2 rev₀ 0))
    Window (k+clock) actual reference →
    ∃ rev', Window k (Source284Relative.run description actual clock)
      (Source284SourceRelocation.lift (entry states)
        (represented (tapeAt (cursor b L out).2
          ((cursor b L out).1::false::false::padding (processed remaining false).length [false,false]))
          rev' (codeState (Shared.Codes.FiniteProgramFrameLoop.empty width) rev'))) := by
  dsimp only
  intro hw
  let zero := Source284EncoderFirstSelection.code enc false
  let one := Source284EncoderFirstSelection.code enc true
  let kept := Source284EncoderMarkerSeed.marker enc
  let remaining := rest++[dummy]
  let N := totalCost zero one remaining false kept
  let frame := Shared.Codes.FiniteProgramFrameLoop.program width
  let frameRows := Source284FiniteRelativeRows.rows frame
  let states := (Source284DetectorProduct.serializerRows zero one).length
  let marks := Source284DetectorProduct.serializerMarks zero one
  let original := Source284ListTables.table (Source284DetectorProduct.serializerRows zero one)
  let continuation := Source284ListTables.table frameRows
  let frameCost := Shared.Codes.FiniteProgramFrameLoop.totalCost width (items enc remaining)
  let clock := N+2+frameCost
  let description := Source284TableEncode.encode (entry states+frameRows.length)
    (table states marks original continuation) 1
  let input := canonical (remaining++L) false kept
  let reference := toSource (lifted .lead (logical input.2 rev₀ 0))
  have ht : Shared.Codes.FiniteProgramTapeEquiv.TapeRel input.2
      (canonical ((rest++[dummy])++L) false kept).2 := by rfl
  obtain ⟨rev,rev',he,hs⟩ := Source284SerializerStrip.serializer_then_strip
    enc x w rest dummy L input rev₀ hbody rfl ht k
  have hw' : Window k (Source284Relative.run description actual clock)
      (Source284Relative.run description reference clock) :=
    Source284Relative.run_window description clock k actual reference hw
  change Source284Relative.run description reference clock = _ at he
  rw [he] at hw'
  have hs' := lift_window k (entry states) _ _ hs
  exact ⟨rev',window_trans k _ _ _ hw' hs'⟩

namespace Fixtures
/-- Different higher bits are allowed on both halves. -/
example : Window 3 ⟨1,2,3⟩ ⟨9,10,3⟩ := by
  change 3 = 3 ∧ 1 % 2^3 = 9 % 2^3 ∧ 2 % 2^3 = 10 % 2^3
  decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284SerializerStripWindow
