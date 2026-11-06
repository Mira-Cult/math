import Shared.Beeping.NPcoNP.Source284HardwireTable
import Shared.Beeping.NPcoNP.Source284LoaderAlgebra

/-! Exact finite rewind phase for the source-relative hardwired input loader.
These statements assume the supplied rewind configuration; the complete
loader, target acceptance, and resource bounds are separate. -/

namespace Shared.Beeping.NPcoNP.Source284HardwireRewind

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra

/-- Every allocated rewind row transfers one low bit, and `k` consecutive
rows perform exactly the specified two-half transfer. -/
theorem rewind_from (bits : List Bool) (original : Nat → Bool → Row)
    (k j left right : Nat) (h : j + k ≤ bits.length) :
    run (table bits original) ⟨left, right, some (bits.length + 1 + j)⟩ k =
      ⟨(transfer k left right).1, (transfer k left right).2,
        some (bits.length + 1 + j + k)⟩ := by
  induction k generalizing j left right with
  | zero => simp [run, transfer]
  | succ k ih =>
    have hj : j < bits.length := by omega
    have hnext : (j + 1) + k ≤ bits.length := by omega
    rw [run_front, rewind_step bits original j left right hj]
    have hh := ih (j + 1) (2 * left + right % 2) (right / 2) hnext
    simpa [transfer, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

/-- From the first rewind row, exactly the input length's number of steps
reach the final turning row. This includes empty input. -/
theorem rewind (bits : List Bool) (original : Nat → Bool → Row)
    (left right : Nat) :
    run (table bits original) ⟨left, right, some (bits.length + 1)⟩ bits.length =
      ⟨(transfer bits.length left right).1, (transfer bits.length left right).2,
        some (2 * bits.length + 1)⟩ := by
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.mul_comm, two_mul] using
    rewind_from bits original bits.length 0 left right (by omega)

end Shared.Beeping.NPcoNP.Source284HardwireRewind
