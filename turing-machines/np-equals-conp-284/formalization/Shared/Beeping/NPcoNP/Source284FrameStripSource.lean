import Shared.Beeping.NPcoNP.Source284TaggedCyclesSource

/-! Source-compiled finite metadata removal. This runs the existing fixed
finite frame-stripping table through every supplied equal-width word with a
charged quadratic upper bound. A caller must construct its initial source
window and pay a physical handoff from any preceding table. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284FrameStripSource

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramFrameLoop (framed words totalCost padding)
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284BitWindow (agree_mono)
open Shared.Beeping.NPcoNP.Source284CompileRecords (compile codeState)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)

/-- Any completed continuing finite-program run is followed by its compiled
numeric source from an arbitrary larger finite window. -/
theorem compiled_tape_window (program : Program) (q q' : Nat) (tape tape' : Tape)
    (rev₀ : Bool) (steps k : Nat) (c : Source284Relative.Config)
    (hv : valid program = true) (hq : q < program.length)
    (hrun : run program (q,tape) steps = some (.inr (q',tape')))
    (hw : Window (k+steps) c (represented tape rev₀ (codeState q rev₀))) :
    ∃ rev, Window k (Source284Relative.run (compile program) c steps)
      (represented tape' rev (codeState q' rev)) := by
  have hrel := Source284FiniteProgramRun.run_related program
    (Source284FiniteProgramRun.closed_of_valid program hv) q tape rev₀ hq steps
  rw [hrun] at hrel
  obtain ⟨rev,hr⟩ := Source284EncoderSourceWindow.live_invert program q' tape' _ hrel
  have h := Source284Relative.run_window (compile program) steps k c
    (represented tape rev₀ (codeState q rev₀)) hw
  rw [hr] at h
  exact ⟨rev,h⟩

/-- The numeric source executes the actual metadata-removal loop and retains
an explicit output window around its continuing exit configuration. -/
theorem frames_source_window (width : Nat) (items : List (Bool × List Bool))
    (hwidth : ∀ item ∈ items, item.2.length = width)
    (kept L R : List Bool) (b rev₀ : Bool) (hk : kept.length = width)
    (k : Nat) (c : Source284Relative.Config)
    (hw : Window (k+totalCost width items) c
      (represented (tapeAt L (b::false::tagged (kept++framed items) ++ false::R))
        rev₀ (codeState 0 rev₀))) :
    ∃ rev, Window k
      (Source284Relative.run (compile (Shared.Codes.FiniteProgramFrameLoop.program width)) c
        (totalCost width items))
      (represented (tapeAt (cursor b L (kept++words items)).2
        ((cursor b L (kept++words items)).1::false::false::padding items.length R))
        rev (codeState (Shared.Codes.FiniteProgramFrameLoop.empty width) rev)) := by
  have hp : 0 < (Shared.Codes.FiniteProgramFrameLoop.program width).length := by
    rw [Shared.Codes.FiniteProgramFrameLoop.length]; omega
  have hr := Shared.Codes.FiniteProgramFrameLoop.run_frames width items hwidth kept L R b hk
  exact compiled_tape_window _ 0 _ _ _ rev₀ _ k c
    (Shared.Codes.FiniteProgramFrameLoop.program_valid width) hp hr hw

/-- A content-independent quadratic budget suffices for the complete
metadata-removal pass. -/
theorem frames_source_polynomial_window (width : Nat) (items : List (Bool × List Bool))
    (hwidth : ∀ item ∈ items, item.2.length = width)
    (kept L R : List Bool) (b rev₀ : Bool) (hk : kept.length = width)
    (k : Nat) (c : Source284Relative.Config)
    (hw : Window (k+(items.length+1)*(7*width+30*((items.length+1)*(width+1))+26)) c
      (represented (tapeAt L (b::false::tagged (kept++framed items) ++ false::R))
        rev₀ (codeState 0 rev₀))) :
    ∃ rev, Window k
      (Source284Relative.run (compile (Shared.Codes.FiniteProgramFrameLoop.program width)) c
        (totalCost width items))
      (represented (tapeAt (cursor b L (kept++words items)).2
        ((cursor b L (kept++words items)).1::false::false::padding items.length R))
        rev (codeState (Shared.Codes.FiniteProgramFrameLoop.empty width) rev)) := by
  have hb := Shared.Codes.FiniteProgramFrameLoop.totalCost_bound width items hwidth
  apply frames_source_window width items hwidth kept L R b rev₀ hk k c
  exact ⟨hw.1,agree_mono (by omega) hw.2.1,agree_mono (by omega) hw.2.2⟩

/-- The metadata-removal input can be the exact tagged buffer produced by
the encoder loop. This theorem still requires a paid control handoff and
prepared source window for this second compiled program. -/
theorem encoder_frames_source_window {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (remaining : List Bool) (first : Bool) (L R : List Bool) (rev₀ : Bool)
    (k : Nat) (c : Source284Relative.Config)
    (hw : Window (k+totalCost width
      ((Source284TaggedCyclesSource.processed remaining first).map
        (fun v => (v,Source284EncoderFirstSelection.code enc v)))) c
      (represented (tapeAt L
        ((Shared.Codes.FiniteProgramTaggedLoop.result
            (Source284EncoderFirstSelection.code enc false)
            (Source284EncoderFirstSelection.code enc true) remaining first
            (Source284EncoderMarkerSeed.marker enc)).1::false::
          tagged ((Shared.Codes.FiniteProgramTaggedLoop.result
            (Source284EncoderFirstSelection.code enc false)
            (Source284EncoderFirstSelection.code enc true) remaining first
            (Source284EncoderMarkerSeed.marker enc)).2) ++ false::R))
        rev₀ (codeState 0 rev₀))) :
    ∃ rev, Window k
      (Source284Relative.run (compile (Shared.Codes.FiniteProgramFrameLoop.program width)) c
        (totalCost width ((Source284TaggedCyclesSource.processed remaining first).map
          (fun v => (v,Source284EncoderFirstSelection.code enc v)))))
      (represented (tapeAt
        (cursor (Shared.Codes.FiniteProgramTaggedLoop.result
          (Source284EncoderFirstSelection.code enc false)
          (Source284EncoderFirstSelection.code enc true) remaining first
          (Source284EncoderMarkerSeed.marker enc)).1 L
          (Source284EncoderMarkerSeed.marker enc ++
            (Source284TaggedCyclesSource.processed remaining first).flatMap
              (Source284EncoderFirstSelection.code enc))).2
        ((cursor (Shared.Codes.FiniteProgramTaggedLoop.result
          (Source284EncoderFirstSelection.code enc false)
          (Source284EncoderFirstSelection.code enc true) remaining first
          (Source284EncoderMarkerSeed.marker enc)).1 L
          (Source284EncoderMarkerSeed.marker enc ++
            (Source284TaggedCyclesSource.processed remaining first).flatMap
              (Source284EncoderFirstSelection.code enc))).1::false::false::
          padding (Source284TaggedCyclesSource.processed remaining first).length R))
        rev (codeState (Shared.Codes.FiniteProgramFrameLoop.empty width) rev)) := by
  let bits := Source284TaggedCyclesSource.processed remaining first
  let items := bits.map (fun v => (v,Source284EncoderFirstSelection.code enc v))
  let kept := Source284EncoderMarkerSeed.marker enc
  let head := (Shared.Codes.FiniteProgramTaggedLoop.result
    (Source284EncoderFirstSelection.code enc false)
    (Source284EncoderFirstSelection.code enc true) remaining first kept).1
  have hwidth : ∀ item ∈ items, item.2.length = width := by
    intro item hi
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hi
    exact Source284TaggedCyclesSource.code_length enc v
  have hk : kept.length = width := Source284EncoderMarkerSeed.marker_length enc
  have hbuf : (Shared.Codes.FiniteProgramTaggedLoop.result
      (Source284EncoderFirstSelection.code enc false)
      (Source284EncoderFirstSelection.code enc true) remaining first kept).2 =
      kept++framed items := Source284TaggedCyclesSource.encoder_result_framed enc remaining first
  have hw' : Window (k+totalCost width items) c
      (represented (tapeAt L (head::false::tagged (kept++framed items) ++ false::R))
        rev₀ (codeState 0 rev₀)) := by
    simpa only [← hbuf] using hw
  have h := frames_source_window width items hwidth kept L R head rev₀ hk k c hw'
  have hwords : words items = bits.flatMap (Source284EncoderFirstSelection.code enc) := by
    simp [words,items,List.flatMap_map]
  simpa only [hwords,items,List.length_map] using h

end Shared.Beeping.NPcoNP.Source284FrameStripSource
