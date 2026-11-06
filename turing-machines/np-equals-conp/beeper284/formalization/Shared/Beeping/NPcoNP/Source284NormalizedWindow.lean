import Shared.Beeping.NPcoNP.Source284ScratchNormalizePipeline
import Shared.Beeping.NPcoNP.Source284PackedGuardWindow
import Shared.Beeping.NPcoNP.Source284CanonicalPairWindow

/-! Connect the actual normalized source tape to the canonical input component
used by the packed verifier. The high tape suffix is retained; agreement is
proved only on the exact finite input window. Pair and certificate packing
still require an implemented source loader. -/
namespace Shared.Beeping.NPcoNP.Source284NormalizedWindow

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame frameBits payloadFold)
open Shared.Beeping.NPcoNP.Source284RawParse (payload)

/-- The parsed payload is determined by the complete numeric input, including
virtual-zero cases; no canonicality assumption on the suffix is needed. -/
theorem payload_encodeFrame (w : List Bool) (suffix : Nat) :
    payload (encodeFrame w suffix).bits = w := by
  have hraw := Source284RawParse.parse_value (encodeFrame w suffix).bits
  rw [Shared.Codes.BinaryAdditionCanonical.value_bits, Source284Parser.parse_encodeFrame] at hraw
  have hl : (payload (encodeFrame w suffix).bits).length = w.length := congrArg Prod.fst hraw |>.symm
  have hf : payloadFold 1 (payload (encodeFrame w suffix).bits) = payloadFold 1 w := (congrArg Prod.snd hraw).symm
  rw [Source284Parser.payloadFold_value,Source284Parser.payloadFold_value,hl] at hf
  have hv : value (payload (encodeFrame w suffix).bits).reverse = value w.reverse := by omega
  have hr := Source284CanonicalPairWindow.same_length_value_injective
    (payload (encodeFrame w suffix).bits).reverse w.reverse (by simpa using hl) hv
  simpa using congrArg List.reverse hr

/-- The canonical framed input fits in its exact delimiter-and-sentinel width. -/
theorem canonical_frame_lt (w : List Bool) : encodeFrame w 1 < 4^(w.length+1) := by
  have h := Source284Witness.value_lt_pow_length (frameBits w [true])
  have he : value (frameBits w [true]) = encodeFrame w 1 := by
    simpa [value] using (Source284Parser.encodeFrame_eq_value w [true]).symm
  rw [he,Source284WitnessWindow.frame_length] at h
  have hp : 2^(2*w.length+2) = 4^(w.length+1) := by
    have h' : 2*w.length+2 = 2*(w.length+1) := by omega
    rw [h',Nat.pow_mul]
  simpa only [hp] using h

/-- The retained high suffix begins strictly after the complete canonical
input frame, so it cannot change its low window. -/
theorem normalized_mod (w : List Bool) (tail : Nat) :
    encodeFrame w (2*tail+1) % 4^(w.length+1) = encodeFrame w 1 := by
  rw [Source284ScratchNormalize.normalized_suffix, Nat.add_mod, Nat.mul_mod,
    Nat.mod_self, zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (canonical_frame_lt w)]
  exact Nat.mod_eq_of_lt (canonical_frame_lt w)

theorem canonical_input_value (input : Nat) :
    value (Source284PackedGuardWindow.inputBits input.bits) =
      encodeFrame (payload input.bits) 1 := by
  unfold Source284PackedGuardWindow.inputBits
  simpa [value] using (Source284Parser.encodeFrame_eq_value (payload input.bits) [true]).symm

/-- Actual source execution reaches the canonical verifier's input component
as a finite low-bit window, while the certificate remains recoverable from
the left tape. This is not the packed pair expected by the verifier. -/
theorem source_window (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ right,
      Source284Relative.run (Source284ScratchNormalizePipeline.description states continuation)
        (Source284Relative.initial input certificate)
        (Source284ScratchNormalizePipeline.totalCost (Source284Parser.length input)) =
          ⟨2*certificate,right,active 210⟩ ∧
      right % 4^(Source284Parser.length input+1) =
        value (Source284PackedGuardWindow.inputBits input.bits) := by
  obtain ⟨w,suffix,hw,hlen,hr⟩ :=
    Source284ScratchNormalizePipeline.source_total_progress states continuation input certificate hn hv
  have hp : payload input.bits = w := by
    rw [← hw]
    exact payload_encodeFrame w suffix
  refine ⟨encodeFrame w (2*(suffix/4)+1),hr,?_⟩
  rw [← hlen,normalized_mod,canonical_input_value,hp]

/-- The modulus is exactly the length of the verifier's canonical input list,
not a guessed buffer size. -/
theorem source_window_exact (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ right,
      Source284Relative.run (Source284ScratchNormalizePipeline.description states continuation)
        (Source284Relative.initial input certificate)
        (Source284ScratchNormalizePipeline.totalCost (Source284Parser.length input)) =
          ⟨2*certificate,right,active 210⟩ ∧
      right % 2^(Source284PackedGuardWindow.inputBits input.bits).length =
        value (Source284PackedGuardWindow.inputBits input.bits) := by
  obtain ⟨right,hr,hw⟩ := source_window states continuation input certificate hn hv
  refine ⟨right,hr,?_⟩
  have hl := Source284PackedGuardWindow.inputBits_length input.bits
  rw [Shared.Codes.BinaryAdditionCanonical.value_bits] at hl
  rw [hl]
  have he : 2^(2*Source284Parser.length input+2) =
      4^(Source284Parser.length input+1) := by
    have h' : 2*Source284Parser.length input+2 =
        2*(Source284Parser.length input+1) := by omega
    rw [h',Nat.pow_mul]
  rw [he]
  exact hw

/-- A bounded bit reader sees exactly the canonical input list. The original
certificate remains in the left half, shifted by one cell. -/
theorem source_window_bits (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ right,
      Source284Relative.run (Source284ScratchNormalizePipeline.description states continuation)
        (Source284Relative.initial input certificate)
        (Source284ScratchNormalizePipeline.totalCost (Source284Parser.length input)) =
          ⟨2*certificate,right,active 210⟩ ∧
      Source284CanonicalPairWindow.window
        (Source284PackedGuardWindow.inputBits input.bits).length right =
          Source284PackedGuardWindow.inputBits input.bits := by
  obtain ⟨right,hr,hw⟩ := source_window_exact states continuation input certificate hn hv
  refine ⟨right,hr,?_⟩
  apply Source284CanonicalPairWindow.same_length_value_injective
  · exact Source284CanonicalPairWindow.window_length _ _
  · rw [Source284CanonicalPairWindow.window_value,hw]

namespace Fixtures

/-- A lone marker supplies a virtual zero payload bit. -/
example : payload (1 : Nat).bits = [false] := by decide +kernel

/-- Retained high suffix data does not change the four-bit input frame. -/
example : encodeFrame [false] (2*97+1) % 16 = 9 := by decide +kernel

example : Source284PackedGuardWindow.inputBits (1 : Nat).bits =
    [true,false,false,true] := by decide +kernel

end Fixtures

end Shared.Beeping.NPcoNP.Source284NormalizedWindow
