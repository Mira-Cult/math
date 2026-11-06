import Shared.Beeping.NPcoNP.Source284HardwireWitness
import Shared.Beeping.NPcoNP.Source284TableCountdown

/-! Exact-clock reduction with a paid hardwired input and finite timeout
guard. The guard is specialized to this input's original clock and goes to a
permanent nonaccepting sink when that clock expires. The source reference
may use a longer clock and a larger certificate search, but its answer below
is the original table's T-step answer with T-bit witnesses. This is an
extensional theorem about supplied table functions; effective serialization,
polynomial running time, SAT hardness, and physical refinement remain open. -/

namespace Shared.Beeping.NPcoNP.Source284HardwireGuarded

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable
open Shared.Beeping.NPcoNP.Source284HardwireWitness
open Shared.Beeping.NPcoNP.Source284TableFrame
open Shared.Beeping.NPcoNP.Source284TableClock
open Shared.Beeping.NPcoNP.Source284HardnessFramePoly
open Shared.Beeping.NPcoNP.Source284Comparison

/-- A hardwired, countdown-guarded table has the original bounded answer
even when the reference's unary clock and certificate search are enlarged.
The larger search is quotiented by low-T-bit agreement, not by asserting
that oversized natural certificates are rejected. -/
theorem reference_guarded_original_bound
    (bits : List Bool) (original : Nat → Bool → Row) (n cutoff : Nat)
    (hn : 0 < n) (hclosed : Closed n original) (extra : Nat)
    (hclock :
      (programBits
        (offset bits + Source284TableCountdown.allocated n cutoff)
        (table bits (Source284TableCountdown.table n cutoff original))).length + 1 ≤
          offset bits + (cutoff+extra)) :
    reference (value (produceSafe
      (programBits (offset bits + Source284TableCountdown.allocated n cutoff)
        (table bits (Source284TableCountdown.table n cutoff original)),
       padFor
        (programBits (offset bits + Source284TableCountdown.allocated n cutoff)
          (table bits (Source284TableCountdown.table n cutoff original)))
        (offset bits+(cutoff+extra))))) = true ↔
      ∃ certificate, certificate < 2^cutoff ∧
        (run original ⟨certificate,value bits,some 0⟩ cutoff).state.isNone = true := by
  have hpositive : 0 < Source284TableCountdown.allocated n cutoff := by
    simp [Source284TableCountdown.allocated]
  have hguard : Closed (Source284TableCountdown.allocated n cutoff)
      (Source284TableCountdown.table n cutoff original) :=
    Source284TableCountdown.closed n cutoff original
  rw [reference_hardwired_original_witness_bound bits
    (Source284TableCountdown.table n cutoff original)
    (Source284TableCountdown.allocated n cutoff) hpositive hguard (cutoff+extra) hclock]
  simp_rw [Source284TableCountdown.initial_acceptance_stable n cutoff original
    hn hclosed _ (value bits) extra]
  constructor
  · rintro ⟨certificate, _, haccept⟩
    refine ⟨certificate % 2^cutoff, Nat.mod_lt _ (by positivity), ?_⟩
    rw [← table_accepts_truncate bits original n hn hclosed certificate cutoff]
    exact haccept
  · rintro ⟨certificate, hsmall, haccept⟩
    refine ⟨certificate, ?_, haccept⟩
    exact lt_of_lt_of_le hsmall
      (Nat.pow_le_pow_right (by decide) (by omega : cutoff ≤ cutoff+extra))

end Shared.Beeping.NPcoNP.Source284HardwireGuarded
