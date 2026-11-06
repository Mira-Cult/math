import Shared.Beeping.NPcoNP.Source284WitnessWindow

/-! A list-level specification for a dynamic witness cutoff. The Boolean
`markers` scans at most the requested number of marker positions and does
not inspect a payload after the last requested marker. This connects the
window decoder's rejection to seeing one marker beyond the allowed witness
length. It does not implement a counter, source-machine wrapper, or clock. -/

namespace Shared.Beeping.NPcoNP.Source284WitnessMarkerCutoff
open Shared.Beeping.NPcoNP.Source284RawParse (payload)

/-- Whether the requested consecutive marker positions are all set. Missing
bits are zero. A lone true marker counts, even without its payload bit. -/
def markers : Nat → List Bool → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | _ + 1, false :: _ => false
  | 1, true :: _ => true
  | _ + 2, [true] => false
  | k + 2, true :: _ :: rest => markers (k + 1) rest

/-- Looking for `m+1` true markers detects a decoded payload longer than `m`. -/
theorem markers_iff (m : Nat) (xs : List Bool) :
    markers (m + 1) xs = true ↔ m < (payload xs).length := by
  induction m generalizing xs with
  | zero =>
    cases xs with
    | nil => simp [markers, payload]
    | cons b bs =>
      cases b <;> cases bs <;> simp [markers, payload]
  | succ m ih =>
    cases xs with
    | nil => simp [markers, payload]
    | cons b bs =>
      cases b with
      | false => simp [markers, payload]
      | true =>
        cases bs with
        | nil => simp [markers, payload]
        | cons b rest =>
          simp only [markers, payload, List.length_cons, Nat.succ_lt_succ_iff]
          exact ih rest
open Shared.Beeping.NPcoNP.Source284WitnessWindow (width decode)

/-- Exact rejection criterion on the decoder's explicitly truncated window.
This does not reject arbitrary high-bit aliases of that window. -/
theorem decode_none_iff (limit certificate : Nat) :
    decode limit certificate = none ↔
      markers (limit + 1) (certificate % 2 ^ width limit).bits = true := by
  rw [markers_iff]
  unfold decode
  dsimp only
  split_ifs with h
  · simp only [Option.some_ne_none, false_iff]
    omega
  · simp only [true_iff]
    omega
end Shared.Beeping.NPcoNP.Source284WitnessMarkerCutoff
