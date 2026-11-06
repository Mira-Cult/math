import Shared.Beeping.NPcoNP.Source284LoaderAlgebra
import Shared.Beeping.NPcoNP.Source284WitnessWindow

/-! Two-stack arithmetic for scanning a delimited witness frame.

The transfer primitive moves one low bit from the second natural-number
half onto the first. These results concern finite arithmetic only: they do
not prove a transition table implements the scanner, a witness-length guard,
or a polynomial-time bound. -/

namespace Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic

open Shared.Beeping.NPcoNP.Source284Parser
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra

/-- Push each marker and payload bit in source order onto the first half. -/
def pushPairs (left : Nat) : List Bool → Nat
  | [] => left
  | b :: bs => pushPairs (4 * left + 2 + (if b then 1 else 0)) bs

/-- A marker/payload frame ending in the zero delimiter occupies exactly
two bits per payload bit and one delimiter bit. -/
theorem frame_length (w : List Bool) : (frameBits w []).length = 2 * w.length + 1 := by
  induction w with
  | nil => rfl
  | cons b bs ih => simp [frameBits, ih] <;> omega

/-- The framed witness is a low-first finite stack followed by the supplied
arbitrary natural suffix. -/
theorem stack_frame (w : List Bool) (suffix : Nat) :
    stack (frameBits w []) suffix = encodeFrame w suffix := by
  induction w with
  | nil => simp [frameBits, stack, encodeFrame]
  | cons b bs ih =>
    simp only [frameBits, stack, encodeFrame, ih]
    cases b <;> simp <;> omega

/-- Pushing a whole frame first pushes each marker and payload, then the
zero delimiter. -/
theorem payloadFold_frame (left : Nat) (w : List Bool) :
    payloadFold left (frameBits w []) = 2 * pushPairs left w := by
  induction w generalizing left with
  | nil => simp [frameBits, payloadFold, pushPairs]
  | cons b bs ih =>
    simp only [frameBits, payloadFold, pushPairs, Bool.true_eq_false, ↓reduceIte]
    have h : 2 * (2 * left + 1) + (if b then 1 else 0) =
        4 * left + 2 + (if b then 1 else 0) := by omega
    rw [h]
    exact ih _

/-- Scanning the marker/payload prefix and delimiter moves precisely those
bits to the first half and leaves the higher suffix unchanged. -/
theorem transfer_frame (left suffix : Nat) (w : List Bool) :
    transfer (2 * w.length + 1) left (encodeFrame w suffix) =
      (2 * pushPairs left w, suffix) := by
  rw [← stack_frame w suffix, ← frame_length w, transfer_stack, payloadFold_frame]

/-- A witness-window encoding uses suffix `1` as its high sentinel. After
scanning its frame, that sentinel is still present as the next unread bit. -/
theorem transfer_witness (left : Nat) (w : List Bool) :
    transfer (2 * w.length + 1) left (Source284WitnessWindow.encode w) =
      (2 * pushPairs left w, 1) := by
  have h : Source284WitnessWindow.encode w = encodeFrame w 1 := by
    simpa [Source284WitnessWindow.encode, Shared.Codes.BitNumeralCompare.value] using
      (encodeFrame_eq_value w [true]).symm
  rw [h]
  exact transfer_frame left 1 w

/-- If the two halves are exchanged after the forward scan, transferring
the same number of bits back restores both the complete original framed
certificate, including its arbitrary high suffix, and the other half. -/
theorem transfer_frame_restore (left suffix : Nat) (w : List Bool) :
    transfer (2 * w.length + 1) suffix (2 * pushPairs left w) =
      (encodeFrame w suffix, left) := by
  have h := transfer_stack (frameBits w []).reverse suffix left
  have hframe : payloadFold suffix (frameBits w []).reverse = encodeFrame w suffix := by
    rw [pushed_eq_stack]
    simpa using stack_frame w suffix
  rw [List.length_reverse, ← pushed_eq_stack (frameBits w []) left,
    frame_length, payloadFold_frame, hframe] at h
  exact h

end Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic
