import Shared.Beeping.NPcoNP.Source284WitnessScanner
import Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic

/-! Positive finite execution of a concrete source-relative witness framing
scanner. The input is the original source's numeric right half, and the
certificate is on the left. All scanned tape bits are written back unchanged.
The run stops at a continuing control boundary after the delimiter. It does
not build a variable-cutoff guard, reconstruct a witness list for a verifier,
or establish a physical 284-state beeper refinement. -/

namespace Shared.Beeping.NPcoNP.Source284WitnessScannerRun

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284WitnessScanner
open Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic
open Shared.Beeping.NPcoNP.Source284Parser
open Shared.Beeping.NPcoNP.Source284Relative

theorem run_add (c : Source284TableRun.Config) (a b : Nat) :
    Source284TableRun.run table c (a+b) =
      Source284TableRun.run table (Source284TableRun.run table c a) b := by
  induction b with
  | zero => simp [Source284TableRun.run]
  | succ b ih =>
    change Source284TableRun.step table (Source284TableRun.run table c (a+b)) =
      Source284TableRun.step table (Source284TableRun.run table (Source284TableRun.run table c a) b)
    rw [ih]

/-- One marker and its payload consume precisely two transitions, preserve
both symbols, and return control to the marker state. -/
theorem marker_payload (left suffix : Nat) (b : Bool) (rest : List Bool) :
    Source284TableRun.run table ⟨left, encodeFrame (b::rest) suffix, some 1⟩ 2 =
      ⟨4*left + 2 + (if b then 1 else 0), encodeFrame rest suffix, some 1⟩ := by
  cases b <;>
    simp [Source284TableRun.run, marker_step, payload_step, encodeFrame,
      Nat.testBit_zero, Nat.add_mod, Nat.mul_mod] <;> congr 1 <;> omega

/-- From the marker state, every framed witness reaches the continuation
after exactly two transitions per payload bit and one for the delimiter. -/
theorem marker_frame (w : List Bool) (left suffix : Nat) :
    Source284TableRun.run table ⟨left, encodeFrame w suffix, some 1⟩ (2*w.length+1) =
      ⟨2*pushPairs left w, suffix, some 3⟩ := by
  induction w generalizing left with
  | nil =>
    simp [Source284TableRun.run, marker_step, encodeFrame, pushPairs, Nat.testBit_zero]
  | cons b bs ih =>
    have htime : 2*(b::bs).length+1 = 2 + (2*bs.length+1) := by simp; omega
    rw [htime, run_add, marker_payload]
    simpa [pushPairs] using ih (4*left+2+(if b then 1 else 0))

/-- The complete scanner begins on the source input, turns onto the
certificate, and reaches its continuation after a positive exact number of
steps. `pushPairs` retains the original input as the high part of the first
half; the frame's unread suffix remains exact. -/
theorem scan_frame (w : List Bool) (input suffix : Nat) :
    Source284TableRun.run table ⟨encodeFrame w suffix, input, some 0⟩ (2*w.length+2) =
      ⟨2*pushPairs input w, suffix, some 3⟩ := by
  have htime : 2*w.length+2 = 1+(2*w.length+1) := by omega
  rw [htime, run_add]
  simp only [Source284TableRun.run, initial_turn]
  exact marker_frame w input suffix

/-- The same result holds for the actual source numeric-table encoding.
The table uses four logical states, eight unary row records, and source
numeric states `1,3,5,7`; these are not physical beeper state counts. -/
theorem source_scan_frame (w : List Bool) (input suffix tail : Nat) :
    Source284Relative.run (encode 4 table tail)
      (Source284Relative.initial input (encodeFrame w suffix)) (2*w.length+2) =
      ⟨2*pushPairs input w, suffix, 7⟩ := by
  rw [source_run, scan_frame]
  rfl

/-- The concrete witness codec's sentinel is the next unread bit. -/
theorem source_scan_witness (w : List Bool) (input tail : Nat) :
    Source284Relative.run (encode 4 table tail)
      (Source284Relative.initial input (Source284WitnessWindow.encode w)) (2*w.length+2) =
      ⟨2*pushPairs input w, 1, 7⟩ := by
  have he : Source284WitnessWindow.encode w = encodeFrame w 1 := by
    simpa [Source284WitnessWindow.encode, Shared.Codes.BitNumeralCompare.value] using
      (encodeFrame_eq_value w [true]).symm
  rw [he]
  exact source_scan_frame w input 1 tail

/-- The two resulting natural halves retain enough information to restore
the complete framed certificate and original numeric input by transferring
the scanned bits back. This is an arithmetic inverse, not yet a source-table
execution of the return pass. -/
theorem source_scanned_halves_restore (w : List Bool) (input suffix tail : Nat) :
    let final := Source284Relative.run (encode 4 table tail)
      (Source284Relative.initial input (encodeFrame w suffix)) (2*w.length+2)
    Shared.Beeping.NPcoNP.Source284LoaderAlgebra.transfer (2*w.length+1)
      final.right final.left = (encodeFrame w suffix, input) := by
  rw [source_scan_frame]
  exact transfer_frame_restore input suffix w

theorem scan_steps_positive (w : List Bool) : 0 < 2*w.length+2 := by omega

end Shared.Beeping.NPcoNP.Source284WitnessScannerRun
