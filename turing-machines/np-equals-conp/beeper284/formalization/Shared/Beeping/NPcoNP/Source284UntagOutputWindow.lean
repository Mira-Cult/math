import Shared.Beeping.NPcoNP.Source284DecodedClearFrameUntag
import Shared.Beeping.NPcoNP.Source284HardnessFrame

/-! Exact blank runway left by untagging. This bounds the window guaranteed
without changing the output tape or assuming a blank original suffix. -/
namespace Shared.Beeping.NPcoNP.Source284UntagOutputWindow

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack stack_value)
open Shared.Beeping.NPcoNP.Source284TaggedMarkerWindow (stack_value_append)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284BitWindow (Agree)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented represented_forward)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.Codes.FinitePrograms (Tape)

def outputTape (words suffix : List Bool) (frames : Nat) : Tape :=
  tapeAt (false::false::Shared.Codes.FiniteProgramUntag.padding words.length (false::suffix))
    (words++false::Shared.Codes.FiniteProgramFrameLoop.padding frames [false,false])

theorem untag_padding (n : Nat) (tail : List Bool) :
    Shared.Codes.FiniteProgramUntag.padding n tail = List.replicate (2*n) false ++ tail := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih =>
    rw [Shared.Codes.FiniteProgramUntag.padding,ih]
    simp [Nat.mul_succ,List.replicate_add,List.append_assoc]

theorem frame_padding (n : Nat) (tail : List Bool) :
    Shared.Codes.FiniteProgramFrameLoop.padding n tail = List.replicate (3*n) false ++ tail := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih =>
    rw [Shared.Codes.FiniteProgramFrameLoop.padding,ih]
    simp [Nat.mul_succ,List.replicate_add,List.append_assoc]

theorem zeros_value (n : Nat) : value (List.replicate n false) = 0 :=
  Source284HardnessFrame.value_replicate_false n

theorem value_blank_prefix (n : Nat) (tail : List Bool) :
    value (List.replicate n false ++ tail) = 2^n * value tail := by
  rw [← stack_value_append,stack_value,zeros_value]
  simp

theorem value_blank_suffix (words : List Bool) (n : Nat) :
    value (words ++ List.replicate n false) = value words := by
  rw [← stack_value_append,stack_value,zeros_value]
  simp

/-- In forward orientation the raw word half is exact; the opposite half
has precisely `2*words.length+3` guaranteed low zero bits. -/
theorem output_halves (words suffix : List Bool) (frames state : Nat) :
    represented (outputTape words suffix frames) false state =
      ⟨2^(2*words.length+3)*value suffix,value words,state⟩ := by
  have hz' : value (Shared.Codes.FiniteProgramFrameLoop.padding frames [false,false]) = 0 := by
    rw [frame_padding,value_blank_prefix]
    simp [Shared.Codes.BitNumeralCompare.value]
  have hv (bs : List Bool) :
      value (bs ++ false::Shared.Codes.FiniteProgramFrameLoop.padding frames [false,false]) = value bs := by
    rw [← stack_value_append,stack_value]
    simp [Shared.Codes.BitNumeralCompare.value,hz']
  have hl : value (false::false::Shared.Codes.FiniteProgramUntag.padding words.length (false::suffix)) =
      2^(2*words.length+3)*value suffix := by
    rw [untag_padding]
    simp only [Shared.Codes.BitNumeralCompare.value, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rw [value_blank_prefix]
    simp [Shared.Codes.BitNumeralCompare.value,pow_add]
    ring
  rw [represented_forward]
  cases words with
  | nil =>
    simp only [outputTape,tapeAt,List.nil_append,List.head?_cons,Option.getD_some,List.tail_cons,
      Source284Relative.Config.mk.injEq, and_true]
    constructor
    · simpa using hl
    · simp [Shared.Codes.BitNumeralCompare.value,hz']
  | cons b bs =>
    simp only [outputTape,tapeAt,List.cons_append,List.head?_cons,Option.getD_some,List.tail_cons,
      Source284Relative.Config.mk.injEq, and_true]
    constructor
    · simpa using hl
    · simp [Shared.Codes.BitNumeralCompare.value,hv]

/-- A reset to the encoder's start state would satisfy the existing encoder
window premise up to this radius, independently of the original suffix.
The reset itself is not claimed here. -/
theorem output_window (words suffix : List Bool) (frames radius : Nat)
    (hr : radius ≤ 2*words.length+3) :
    Window radius (represented (outputTape words suffix frames) false 1)
      (Source284Relative.initial (value words) 0) := by
  rw [output_halves]
  refine ⟨rfl,?_,?_⟩
  · have hd : 2^radius ∣ 2^(2*words.length+3)*value suffix :=
      dvd_mul_of_dvd_left (pow_dvd_pow 2 hr) _
    simp [Agree,Source284Relative.initial,Nat.mod_eq_zero_of_dvd hd]
  · rfl


/-- The uniform runway bound is sharp: a one immediately above it is
visible in the next larger window. -/
theorem next_cell_can_be_nonblank (words : List Bool) (frames : Nat) :
    ¬ Window (2*words.length+4) (represented (outputTape words [true] frames) false 1)
      (Source284Relative.initial (value words) 0) := by
  rw [output_halves]
  intro h
  have he := h.2.1
  have hp : 0 < 2^(2*words.length+3) := pow_pos (by decide) _
  have hpow : 2^(2*words.length+4) = 2^(2*words.length+3)*2 := by
    convert (pow_succ 2 (2*words.length+3)) using 1
  have hlt : 2^(2*words.length+3) < 2^(2*words.length+4) := by
    rw [hpow]
    omega
  simp [Agree,Source284Relative.initial,Shared.Codes.BitNumeralCompare.value,
    Nat.mod_eq_of_lt hlt] at he

end Shared.Beeping.NPcoNP.Source284UntagOutputWindow
