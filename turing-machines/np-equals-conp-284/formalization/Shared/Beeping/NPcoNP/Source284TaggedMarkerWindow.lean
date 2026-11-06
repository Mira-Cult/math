import Shared.Beeping.NPcoNP.Source284TaggedMarkerSeed

/-! Exact relationship between the paid tagged marker and the prepared
serializer's source window. The remaining low-zero condition on the old
scratch suffix is explicit. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284TaggedMarkerWindow

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284BitWindow (Agree)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284TableRun (toSource)
open Shared.Beeping.NPcoNP.Source284DetectorProduct (lifted)
open Shared.Beeping.NPcoNP.Source284SerializerTrace (logical)
open Shared.Codes.FiniteProgramTaggedLoop (canonical)

/-- Appending a finite list to a low-first stack gives its binary value. -/
theorem stack_value_append (xs ys : List Bool) : stack xs (value ys) = value (xs++ys) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.cons_append,stack,value,ih]

/-- A common finite prefix preserves agreement of the supplied high tails. -/
theorem stack_agree (k : Nat) (xs : List Bool) (a b : Nat) (h : Agree k a b) :
    Agree k (stack xs a) (stack xs b) := by
  rw [Source284LoaderAlgebra.stack_value,Source284LoaderAlgebra.stack_value]
  exact Nat.ModEq.add_right (value xs) (Nat.ModEq.mul_left (2^xs.length) h)

/-- The fixed marker seed supplies the exact required low marker, the raw
body, and the relative orientation. Only the specified low window of the
remaining old scratch suffix must already be zero. -/
theorem seeded_window {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      Source284JoinedRawEncodeTM2.machine → List.Vector Bool width)
    (rest L : List Bool) (dummy : Bool) (scratch k : Nat)
    (hblank : Agree k (2*(scratch/2^((Source284TaggedMarkerSeed.word enc).length+1))) 0) :
    let word := Source284TaggedMarkerSeed.word enc
    let start := Nat.pair (Source284JoinedEndDetectorTable.index .lead)
      (Source284FiniteRelativeRows.index 0 true)
    let actual := toSource ⟨stack word (2*(scratch/2^(word.length+1))),
      stack (false::rest) (stack [dummy] (value L)),some start⟩
    let expected := toSource (lifted .lead
      (logical (canonical ((rest++[dummy])++L) false (Source284EncoderMarkerSeed.marker enc)).2 true 0))
    Window k actual expected := by
  dsimp only
  let word := Source284TaggedMarkerSeed.word enc
  have hs := stack_agree k word (2*(scratch/2^(word.length+1))) 0 hblank
  have hword : stack word 0 = value
      (false::Shared.Codes.FiniteProgramBitShuttle.tagged (Source284EncoderMarkerSeed.marker enc) ++
        [false,false,false]) := by
    change stack word (value [false,false,false]) = _
    rw [stack_value_append]
    rfl
  rw [hword] at hs
  have hbody : stack (false::rest) (stack [dummy] (value L)) =
      value (false::((rest++[dummy])++L)) := by
    rw [stack_value_append,stack_value_append]
    simp [List.append_assoc]
  refine ⟨?_,?_,?_⟩
  · simp [toSource,lifted,logical,Source284FiniteRelativeRows.index,
      Source284CompileRecords.bit]
  · simpa [toSource,lifted,logical,Source284FiniteTapeStep.represented,
      Source284FiniteTapeStep.value_eq_shared,canonical,
      Shared.ComplexityBridge.PairMarkedScanner.tapeAt,word] using hs
  · simp [toSource,lifted,logical,Source284FiniteTapeStep.represented,
      Source284FiniteTapeStep.value_eq_shared,canonical,
      Shared.ComplexityBridge.PairMarkedScanner.tapeAt,hbody,Agree,value,
      Source284FiniteTapeStep.digit]

end Shared.Beeping.NPcoNP.Source284TaggedMarkerWindow
