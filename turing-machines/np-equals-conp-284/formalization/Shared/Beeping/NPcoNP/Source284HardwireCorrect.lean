import Shared.Beeping.NPcoNP.Source284HardwireWrite
import Shared.Beeping.NPcoNP.Source284HardwireRewind

/-! Exact execution of the source-relative fixed-input loader. The supplied
input is paid for with `2*bits.length+2` allocated logical table states and
transitions; the certificate is initially on the left half and is preserved.
These are not physical 284-state counts. This is not a clock-inflation theorem,
an effective compiler, or an NP-hardness proof. -/

namespace Shared.Beeping.NPcoNP.Source284HardwireCorrect

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable
open Shared.Beeping.NPcoNP.Source284HardwireWrite
open Shared.Beeping.NPcoNP.Source284HardwireRewind
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra

theorem run_add (t : Nat → Bool → Row) (c : Config) (m n : Nat) :
    run t c (m+n) = run t (run t c m) n := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    change step t (run t c (m+n)) = step t (run t (run t c m) n)
    rw [ih]

/-- The loader writes the fixed input, retraces it, and turns back across
the first certificate cell. Both turns are charged, even for an empty input. -/
theorem loader_run (bits : List Bool) (original : Nat → Bool → Row)
    (certificate : Nat) :
    run (table bits original) ⟨certificate,0,some 0⟩ (offset bits) =
      ⟨certificate,value bits,some (offset bits)⟩ := by
  let t := table bits original
  let m := bits.length
  have hw : run t ⟨certificate,0,some 0⟩ m =
      ⟨payloadFold certificate bits,0,some m⟩ := write_input original bits certificate
  have hfirst : run t ⟨certificate,0,some 0⟩ (m+1) =
      ⟨0,payloadFold certificate bits,some (m+1)⟩ := by
    rw [run, hw]
    exact outward_turn_step bits original _
  have hr := rewind bits original 0 (payloadFold certificate bits)
  rw [push_transfer bits certificate] at hr
  have hback : run t ⟨certificate,0,some 0⟩ (m+1+m) =
      ⟨value bits,certificate,some (2*m+1)⟩ := by
    rw [run_add, hfirst]
    exact hr
  have hoff : offset bits = m+1+m+1 := by simp [offset, m]; omega
  rw [hoff, run, hback]
  simpa [offset, m, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, two_mul] using
    return_turn_step bits original (value bits) certificate

/-- Every following original step is simulated in its relocated state;
the result counts all initialization steps and preserves acceptance. -/
theorem loader_then_run (bits : List Bool) (original : Nat → Bool → Row)
    (certificate clock : Nat) :
    run (table bits original) ⟨certificate,0,some 0⟩ (offset bits + clock) =
      shiftConfig (offset bits) (run original ⟨certificate,value bits,some 0⟩ clock) := by
  rw [run_add, loader_run]
  change run (table bits original)
    (shiftConfig (offset bits) ⟨certificate,value bits,some 0⟩) clock = _
  exact relocated_run bits original _ clock

/-- The finite numerical source program produced by the existing record
encoder accepts exactly when the original table accepts, with the exact
loader overhead charged. This is an equal-clock statement and does not allow
additional computation after an original timeout. -/
theorem encoded_acceptance (bits : List Bool) (original : Nat → Bool → Row)
    (n : Nat) (hn : 0 < n) (hclosed : Closed n original)
    (tail certificate clock : Nat) :
    Source284Relative.accepts (encode (offset bits+n) (table bits original) tail)
      0 certificate (offset bits+clock) =
        (run original ⟨certificate,value bits,some 0⟩ clock).state.isNone := by
  rw [bounded_acceptance (offset bits+n) (table bits original) tail
    (by dsimp [offset]; omega) (closed bits original n hn hclosed)]
  rw [loader_then_run]
  change ((run original ⟨certificate,value bits,some 0⟩ clock).state.map
    (fun q => offset bits + q)).isNone = _
  cases h : (run original ⟨certificate,value bits,some 0⟩ clock).state <;> simp [h]

end Shared.Beeping.NPcoNP.Source284HardwireCorrect
