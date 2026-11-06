import Shared.Beeping.NPcoNP.Source284HardwireTable
import Shared.Beeping.NPcoNP.Source284Suffix

/-! The outward writing phase of the fixed-input relative-table loader.
It uses no unindexed initialization and preserves the higher certificate
tail as part of the explicit left-half numeral. The return phase is separate. -/

namespace Shared.Beeping.NPcoNP.Source284HardwireWrite

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)

/-- Starting after an already-written prefix, each remaining input bit is
written in order. The source table ignores the initial symbol on the blank
right half, and each step advances to the next explicit loader state. -/
theorem write_suffix (original : Nat → Bool → Row) (pre rest : List Bool)
    (left : Nat) :
    run (table (pre ++ rest) original) ⟨left, 0, some pre.length⟩ rest.length =
      ⟨payloadFold left rest, 0, some (pre ++ rest).length⟩ := by
  induction rest generalizing pre left with
  | nil => simp [run, payloadFold]
  | cons b bs ih =>
    have hi : pre.length < (pre ++ b :: bs).length := by simp
    have hv : (((pre ++ b :: bs)[pre.length]?).getD false) = b := by
      rw [List.getElem?_append_right (by omega)]
      simp
    have hfirst := writing_step (pre ++ b :: bs) original pre.length left hi
    rw [hv] at hfirst
    have hnext := ih (pre ++ [b]) (2*left + bit b)
    simp only [List.length_append, List.length_singleton] at hnext
    rw [List.length_cons, run_front, hfirst]
    simpa [List.append_assoc, payloadFold, bit,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext

/-- From the loader start, the outward write completes in exactly the
number of supplied input bits, including the zero-bit case. -/
theorem write_input (original : Nat → Bool → Row) (bits : List Bool)
    (certificate : Nat) :
    run (table bits original) ⟨certificate, 0, some 0⟩ bits.length =
      ⟨payloadFold certificate bits, 0, some bits.length⟩ := by
  simpa using write_suffix original [] bits certificate

end Shared.Beeping.NPcoNP.Source284HardwireWrite
