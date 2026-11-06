import Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral

/-! Variable-length unary selector word identities for the shortened cycle. -/
namespace Shared.Beeping.NPcoNP.NativeVariableWindowWords
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

theorem zero_window_prefix (k : Nat) :
    markerWindow (List.replicate k 0 ++ [0]) = false :: (encode (List.replicate k 0) ++ [true]) := by
  apply List.append_cancel_right (bs := [false])
  have h := markerWindow_append_zero (List.replicate k 0 ++ [0])
  simpa [encode_append,encode,block,List.append_assoc] using h

/-- The unit scan's physical word before its last omitted delimiter. -/
theorem variable_unit_window_word (k r : Nat) :
    markerWindow (List.replicate (k+1) 0 ++ [1,0,r]) =
      ([false,true] ++ markerWindow (List.replicate k 0 ++ [0])) ++
        [true,false,true,false] ++ List.replicate (r+1) true := by
  rw [zero_window_prefix]
  apply List.append_cancel_right (bs := [false])
  have h1 := markerWindow_append_zero (List.replicate (k+1) 0 ++ [1,0,r])
  simpa [List.replicate_succ,encode_append,encode,block,List.append_assoc] using h1

/-- The positive scan's physical word before its last omitted delimiter. -/
theorem variable_positive_window_word (k r : Nat) :
    markerWindow (List.replicate (k+1) 0 ++ [3,r]) =
      ([false,true] ++ markerWindow (List.replicate k 0 ++ [0])) ++
        [true,true,true,false] ++ List.replicate (r+1) true := by
  rw [zero_window_prefix]
  apply List.append_cancel_right (bs := [false])
  have h1 := markerWindow_append_zero (List.replicate (k+1) 0 ++ [3,r])
  simpa [List.replicate_succ,encode_append,encode,block,List.append_assoc] using h1

#print axioms variable_unit_window_word
#print axioms variable_positive_window_word
end Shared.Beeping.NPcoNP.NativeVariableWindowWords
