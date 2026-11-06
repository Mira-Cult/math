import Shared.Beeping.NPcoNP.Source284WitnessScannerRun
import Shared.Beeping.NPcoNP.Source284WitnessMarkerCutoff

/-! The concrete source scanner exposes the bounded-window cutoff marker
at a fixed transition boundary. This does not implement a cutoff counter,
restore the input tape, or prove a bit-cost bound. -/
namespace Shared.Beeping.NPcoNP.Source284ScannerCutoffBridge
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284WitnessScanner
open Shared.Beeping.NPcoNP.Source284WitnessScannerRun
open Shared.Beeping.NPcoNP.Source284WitnessMarkerCutoff
open Shared.Codes.BitNumeralCompare (value)

set_option maxHeartbeats 2000000

theorem continuation_state (left right n : Nat) :
    (Source284TableRun.run table ⟨left, right, some 3⟩ n).state = some 3 := by
  induction n generalizing left right with
  | zero => rfl
  | succ n ih =>
    rw [show n+1 = 1 + n by omega, run_add]
    simpa [Source284TableRun.run, continuation_step] using ih (2*left + right % 2) (right / 2)

open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

theorem marker_state (m : Nat) (w : List Bool) (left suffix : Nat) :
    (Source284TableRun.run table ⟨left, encodeFrame w suffix, some 1⟩ (2*m+1)).state = some 2 ↔
      m < w.length := by
  induction m generalizing w left with
  | zero =>
    cases w with
    | nil => simp [Source284TableRun.run, marker_step, encodeFrame, Nat.testBit_zero]
    | cons b bs =>
      cases b <;> simp [Source284TableRun.run, marker_step, encodeFrame, Nat.testBit_zero, Nat.add_mod, Nat.mul_mod]
  | succ m ih =>
    cases w with
    | nil =>
      have ht : 2*(m+1)+1 = 1 + (2*m+2) := by omega
      rw [ht, run_add]
      change (Source284TableRun.run table (Source284TableRun.step table ⟨left, encodeFrame [] suffix, some 1⟩) (2*m+2)).state = some 2 ↔ _
      have hs : Source284TableRun.step table ⟨left, encodeFrame [] suffix, some 1⟩ = ⟨2*left, suffix, some 3⟩ := by
        simp [marker_step, encodeFrame, Nat.testBit_zero]
      rw [hs, continuation_state]
      simp
    | cons b bs =>
      have ht : 2*(m+1)+1 = 2 + (2*m+1) := by omega
      rw [ht, run_add, marker_payload]
      simpa using ih bs (4*left+2+(if b then 1 else 0))

/-- The actual encoded source reaches its payload state on the (m+1)st
marker exactly when the frame contains more than m payloads. -/
theorem source_frame_marker (m : Nat) (w : List Bool) (input suffix tail : Nat) :
    (Source284Relative.run (encode 4 table tail)
      (Source284Relative.initial input (encodeFrame w suffix)) (2*m+2)).state = 5 ↔
      m < w.length := by
  rw [source_run]
  have ht : 2*m+2 = 1+(2*m+1) := by omega
  rw [ht, run_add]
  change nextState (Source284TableRun.run table
    (Source284TableRun.step table ⟨encodeFrame w suffix, input, some 0⟩) (2*m+1)).state = 5 ↔ _
  rw [initial_turn]
  have hs := marker_state m w input suffix
  have he (q : Option Nat) : nextState q = 5 ↔ q = some 2 := by
    cases q with
    | none => simp [nextState]
    | some k => simp only [nextState, active, Option.some.injEq]; omega
  rw [he]
  exact hs

/-- The encoded scanner examines only the explicitly truncated low window.
The theorem does not say the original, untruncated tape was changed. -/
theorem source_window_reject (limit certificate input tail : Nat) :
    let window := certificate % 2 ^ Source284WitnessWindow.width limit
    (Source284Relative.run (encode 4 table tail)
      (Source284Relative.initial input window) (2*limit+2)).state = 5 ↔
      Source284WitnessWindow.decode limit certificate = none := by
  dsimp only
  let window := certificate % 2 ^ Source284WitnessWindow.width limit
  obtain ⟨w, suffix, hw⟩ := Source284Parser.encodeFrame_surjective window
  have hlen : Source284Parser.length window = w.length := by
    rw [← hw]
    simp [Source284Parser.length, Source284Parser.parse_encodeFrame]
  have hp : (Source284RawParse.payload window.bits).length = w.length := by
    have hh := Source284RawParse.parse_length window.bits
    rw [Shared.Codes.BinaryAdditionCanonical.value_bits] at hh
    omega
  change (Source284Relative.run (encode 4 table tail)
    (Source284Relative.initial input window) (2*limit+2)).state = 5 ↔ _
  rw [← hw, source_frame_marker]
  rw [Source284WitnessMarkerCutoff.decode_none_iff, Source284WitnessMarkerCutoff.markers_iff]
  change limit < w.length ↔ limit < (Source284RawParse.payload window.bits).length
  rw [hp]

end Shared.Beeping.NPcoNP.Source284ScannerCutoffBridge
