import Shared.Beeping.NPcoNP.Source284ClearTape
import Shared.Beeping.NPcoNP.Source284FrameStripSource
import Shared.Codes.FiniteProgramMirror

/-! The paid reflected untagger at the cleared frame-output boundary. This
proves its source run and exact serialized words; linking frame control to
untagger control remains a separate obligation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284ClearedUntagSource

open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284CompileRecords (compile codeState)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)

/-- The frame-removal output words are precisely the joined encoder's
serialized input, including its fixed leading symbol. -/
theorem serialized_words {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (x w rest : List Bool) (dummy : Bool)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest) :
    Source284EncoderMarkerSeed.marker enc ++
      (processed (rest++[dummy]) false).flatMap (Source284EncoderFirstSelection.code enc) =
      Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits Source284JoinedRawEncodeTM2.machine enc
        (Source284JoinedFrames.joinedBits x w) := by
  rw [Source284SerializerTrace.processed_append,← hbody]
  exact (Source284EncoderMarkerSeed.marker_is_serialized_prefix enc x w).symm

/-- The actual finite relative-source program untags the frame output and
positions the head on the first raw word bit. Both source and output high
suffixes remain explicit; the charged run is quadratic in the word length. -/
theorem untag_source_window (words L R : List Bool) (rev₀ : Bool) (k : Nat)
    (c : Source284Relative.Config)
    (hw : Window (k+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)) c
      (represented (tapeAt (cursor false (false::L) words).2
        ((cursor false (false::L) words).1::false::false::R)) rev₀ (codeState 0 rev₀))) :
    ∃ rev, Window k
      (Source284Relative.run (compile Shared.Codes.FiniteProgramMirror.positioned) c
        (2+Shared.Codes.FiniteProgramUntag.cost words.reverse))
      (represented (tapeAt
        (false::false::Shared.Codes.FiniteProgramUntag.padding words.length (false::L))
        (words++false::R)) rev (codeState 14 rev)) := by
  have hpos : 0 < Shared.Codes.FiniteProgramMirror.positioned.length := by
    rw [Shared.Codes.FiniteProgramMirror.positioned_length]; omega
  have hr := Shared.Codes.FiniteProgramMirror.positioned_run words L R
  exact Source284FrameStripSource.compiled_tape_window _ 0 14 _ _ rev₀ _ k c
    Shared.Codes.FiniteProgramMirror.positioned_valid hpos hr hw

theorem untag_cost_bound (words : List Bool) :
    2+Shared.Codes.FiniteProgramUntag.cost words.reverse ≤ words.length*(20*words.length+21)+6 :=
  Shared.Codes.FiniteProgramMirror.positioned_cost_bound words

end Shared.Beeping.NPcoNP.Source284ClearedUntagSource
