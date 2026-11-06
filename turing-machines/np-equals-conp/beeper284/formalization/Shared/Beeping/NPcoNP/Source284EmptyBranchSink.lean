import Shared.Beeping.NPcoNP.Source284EmptyBranchAdapter
import Shared.Beeping.NPcoNP.Source284GuardedSinkCoverage

/-! The empty-prefix adapter preserves a verifier's explicit reject sink.
No cutoff counter or canonical-to-source compiler is constructed here. -/
namespace Shared.Beeping.NPcoNP.Source284EmptyBranchSink

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284EmptyBranchAdapter

/-- A logical reject sink becomes the corresponding odd source state, with
both encoded rows staying in that state for arbitrary tapes. -/
theorem encoded_sink_invariant (original : Nat → Bool → Row) (n tail sink : Nat)
    (hs : sink < n)
    (hzero : (original sink false).next = some sink)
    (hone : (original sink true).next = some sink) :
    ∀ c : Source284Relative.Config,
      c.state = active (2+sink) →
        (Source284Relative.step (encode (n+2) (table original) tail) c).state = active (2+sink) := by
  apply Source284Comparison.invariant_of_records
  · simp [active]
  · have h := record_lookup (n+2) (table original) tail (2+sink) (by omega) false
    have h' := congrArg (fun x : Nat => x/4) h
    simpa [bit,relocated_row,rowCode_next,shiftRow,hzero,nextState] using h'
  · have h := record_lookup (n+2) (table original) tail (2+sink) (by omega) true
    have h' := congrArg (fun x : Nat => x/4) h
    have hi : active (2+sink)-1+bit true = active (2+sink) := by simp [active,bit]
    rw [hi] at h'
    simpa [relocated_row,rowCode_next,shiftRow,hone,nextState] using h'

/-- If the original logical run has accepted or reached its reject sink,
the adapted encoded source run has done so two iterations later. -/
theorem encoded_odd_finished (original : Nat → Bool → Row) (n tail sink input certificate fuel : Nat)
    (hn : 0 < n) (hclosed : Closed n original) (hodd : input % 2 = 1)
    (hfinish : (run original ⟨certificate,input,some 0⟩ fuel).state = none ∨
      (run original ⟨certificate,input,some 0⟩ fuel).state = some sink) :
    (Source284Relative.run (encode (n+2) (table original) tail)
      (Source284Relative.initial input certificate) (fuel+2)).state = 0 ∨
    (Source284Relative.run (encode (n+2) (table original) tail)
      (Source284Relative.initial input certificate) (fuel+2)).state = active (2+sink) := by
  have hv : Valid (n+2) ⟨certificate,input,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    omega
  have h := run_toSource (n+2) (table original) tail ⟨certificate,input,some 0⟩
    (closed original n hn hclosed) hv (fuel+2)
  change Source284Relative.run (encode (n+2) (table original) tail)
    (Source284Relative.initial input certificate) (fuel+2) = _ at h
  rw [odd_initial_run original input certificate fuel hodd] at h
  rcases hfinish with hfinish | hfinish
  · left
    rw [h]
    simp [toSource,shiftConfig,hfinish,nextState]
  · right
    rw [h]
    simp [toSource,shiftConfig,hfinish,nextState]

end Shared.Beeping.NPcoNP.Source284EmptyBranchSink
