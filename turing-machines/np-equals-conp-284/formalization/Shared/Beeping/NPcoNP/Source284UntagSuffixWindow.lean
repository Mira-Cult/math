import Shared.Beeping.NPcoNP.Source284FixedSerializerEncoder
import Shared.Beeping.NPcoNP.Source284CanonicalTaggedPipeline

/-! Exact contribution of the retained input suffix to the untagged output
window. This identifies when additional cleared cells are needed; it does
not itself clear or normalize the source input. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284UntagSuffixWindow

open Shared.Codes.FinitePrograms
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284BitWindow (Agree)
open Shared.Beeping.NPcoNP.Source284FiniteTapeStep (represented)
open Shared.Beeping.NPcoNP.Source284UntagOutputWindow (outputTape output_halves)

def runway (words : List Bool) : Nat := 2*words.length+3

/-- The exact window condition is divisibility of the retained suffix after
accounting for the zero cells created by the untagger. -/
theorem output_window_iff (words suffix : List Bool) (frames radius : Nat) :
    Window radius (represented (outputTape words suffix frames) false 1)
      (Source284Relative.initial (value words) 0) ↔
      2^radius ∣ 2^(runway words)*value suffix := by
  rw [output_halves]
  simp [Window,Agree,Source284Relative.initial,runway,Nat.dvd_iff_mod_eq_zero]

/-- Beyond the already guaranteed runway, exactly the additional suffix
bits in the requested radius must be zero. -/
theorem output_window_iff_suffix (words suffix : List Bool) (frames radius : Nat)
    (hr : runway words ≤ radius) :
    Window radius (represented (outputTape words suffix frames) false 1)
      (Source284Relative.initial (value words) 0) ↔
      2^(radius-runway words) ∣ value suffix := by
  rw [output_window_iff]
  have hpow : 2^radius = 2^(runway words)*2^(radius-runway words) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow, Nat.mul_dvd_mul_iff_left (pow_pos (by decide) _)]

/-- The exact suffix condition also covers radii inside the guaranteed
runway: then the subtracted exponent is zero. -/
theorem output_window_iff_suffix_all (words suffix : List Bool) (frames radius : Nat) :
    Window radius (represented (outputTape words suffix frames) false 1)
      (Source284Relative.initial (value words) 0) ↔
      2^(radius-runway words) ∣ value suffix := by
  by_cases h : runway words ≤ radius
  · exact output_window_iff_suffix words suffix frames radius h
  · have hd : radius-runway words = 0 := Nat.sub_eq_zero_of_le (by omega)
    have hw := Shared.Beeping.NPcoNP.Source284UntagOutputWindow.output_window
      words suffix frames radius (by dsimp [runway] at h; omega)
    simp [hd,hw]

/-- A zero retained suffix supplies every finite encoder window, without a
bound relating the encoder clock to the raw word length. -/
theorem output_window_blank (words suffix : List Bool) (frames radius : Nat)
    (hzero : value suffix = 0) :
    Window radius (represented (outputTape words suffix frames) false 1)
      (Source284Relative.initial (value words) 0) := by
  rw [output_window_iff,hzero]
  simp

/-- A sufficient suffix zero prefix extends the untagger's guaranteed
runway by its own length. -/
theorem output_window_extended (words suffix : List Bool) (frames radius extra : Nat)
    (hzero : 2^extra ∣ value suffix) (hsize : radius ≤ runway words+extra) :
    Window radius (represented (outputTape words suffix frames) false 1)
      (Source284Relative.initial (value words) 0) := by
  rw [output_window_iff]
  have hd : 2^radius ∣ 2^(runway words+extra) := pow_dvd_pow 2 hsize
  exact dvd_trans hd (by rw [pow_add]; exact Nat.mul_dvd_mul_left _ hzero)

/-- The input suffix consumed by the decoded joined-source path contributes
its high bits after three low bits have been discarded. -/
theorem decoded_suffix_value (inputSuffix : Nat) :
    value ((inputSuffix/4).bits.tail) = inputSuffix/8 := by
  rw [← Nat.div2_bits_eq_tail,Shared.Codes.BinaryAdditionCanonical.value_bits]
  simp [Nat.div2_val]
  omega

theorem decoded_suffix_blank (inputSuffix : Nat) (h : inputSuffix < 8) :
    value ((inputSuffix/4).bits.tail) = 0 := by
  rw [decoded_suffix_value]
  exact Nat.div_eq_of_lt h


/-- The canonical frame of every payload has a unique decoded suffix of
one, so its retained suffix contributes no high one bits. -/
theorem canonical_input_suffix (x : List Bool) (inputSuffix : Nat)
    (h : Source284Parser.encodeFrame x 1 = Source284Parser.encodeFrame
      (Source284RawParse.payload (Source284Parser.encodeFrame x 1).bits) inputSuffix) :
    inputSuffix = 1 ∧ value ((inputSuffix/4).bits.tail) = 0 := by
  rw [Source284NormalizedWindow.payload_encodeFrame] at h
  have he := Source284CanonicalTaggedPipeline.frame_suffix_injective x h
  have hs : inputSuffix = 1 := he.symm
  exact ⟨hs,decoded_suffix_blank inputSuffix (by omega)⟩

/-- Every payload also has high-suffix aliases with a nonzero retained bit.
These aliases have the same parsed payload; this alone says nothing about
whether an arbitrary candidate verifier treats their numeric inputs alike. -/
theorem high_alias_needs_padding (x : List Bool) (n : Nat) :
    Source284RawParse.payload (Source284Parser.encodeFrame x (8*2^n)).bits = x ∧
      ¬ 2^(n+1) ∣ value (((8*2^n)/4).bits.tail) := by
  refine ⟨Source284NormalizedWindow.payload_encodeFrame x _,?_⟩
  rw [decoded_suffix_value]
  have hdiv : (8*2^n)/8 = 2^n := by omega
  rw [hdiv,pow_succ]
  intro hd
  have hp : 0 < 2^n := pow_pos (by decide) _
  have hd' : 2^n*2 ∣ 2^n*1 := by simpa using hd
  have h := (Nat.mul_dvd_mul_iff_left hp).1 hd'
  norm_num at h

end Shared.Beeping.NPcoNP.Source284UntagSuffixWindow
