import Shared.Beeping.NPcoNP.Source284PolynomialRunwayCleanup
import Shared.Beeping.NPcoNP.Source284EraseMarkedHistory

/-! The polynomial cleanup that records all removed cells as a unary scratch
counter, allowing the workspace to be moved back by a paid counted shift. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284PolynomialMarkedCleanup

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284ProductIteration (outerAfter historyAfter)
open Shared.Beeping.NPcoNP.Source284PositivePolynomialRunway (block)
open Shared.Beeping.NPcoNP.Source284PolynomialRunwayCleanup (zeros cleanupCost totalCost)
open Shared.Beeping.NPcoNP.Source284ScratchMarkedLoop (marks)

def table (k : Nat) (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284EraseMarkedBlock.table (Source284EraseMarkedHistory.table k continuation)

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284PositivePolynomialTwoSided.description k (30+30*k+states) (table k continuation)

def count (k n : Nat) : Nat :=
  Source284EraseTokenHistory.cells k (n+2) (n+2)+(zeros k n+2)

theorem closed (k states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (30+30*k+states) (table k continuation) := by
  have hh := Source284EraseMarkedHistory.closed k states continuation hn hv
  have hz := Source284EraseMarkedBlock.closed (30*k+states)
    (Source284EraseMarkedHistory.table k continuation) (by omega) hh
  simpa [table,show 30+(30*k+states)=30+30*k+states by omega] using hz

/-- A finite run restores the exact certificate and leaves one scratch mark
for each cell taken from the original gap and the temporary block history. -/
theorem source_then (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate)
      (totalCost k w+fuel) =
    toSource (shiftConfig (664+317*k) (run continuation
      ⟨certificate,2*flipped (w++[false])
        (marks (count k w.length)
          (2^(block k w.length+1)*Source284PositivePolynomialTwoSided.retained k w.length suffix)),
        some 0⟩ fuel)) := by
  have hc := closed k states continuation hn hv
  have h := Source284PositivePolynomialTwoSided.source_then k (30+30*k+states)
    (table k continuation) w certificate suffix (cleanupCost k w+fuel) (by omega) hc
  have ht : totalCost k w+fuel = Source284PositivePolynomialTwoSided.totalCost k w+
      (cleanupCost k w+fuel) := by simp [totalCost,Source284PolynomialRunwayCleanup.totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284PositivePolynomialTwoSided.description k
    (30+30*k+states) (table k continuation)) _ _ = _
  rw [h]
  simp only [cleanupCost,Source284PolynomialRunwayCleanup.cleanupCost,table]
  rw [Source284PolynomialRunwayCleanup.top_form]
  change toSource (shiftConfig (634+287*k)
    (run (Source284EraseMarkedBlock.table (Source284EraseMarkedHistory.table k continuation))
      ⟨2^(zeros k w.length+1)*
        (2*historyAfter k (w.length+2) (w.length+2) certificate+1),_,some 0⟩ _)) = _
  rw [show Source284EraseZeroBlock.cost (zeros k w.length) (w++[false]).length+
      Source284EraseTokenHistory.cost k (w.length+2) (w.length+2) (w++[false]).length+fuel =
      Source284EraseZeroBlock.cost (zeros k w.length) (w++[false]).length+
        (Source284EraseTokenHistory.cost k (w.length+2) (w.length+2) (w++[false]).length+fuel) by omega]
  rw [Source284EraseMarkedBlock.erase_then,Source284EraseMarkedHistory.erase_then]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have hs : 634+287*k+30+30*k=664+317*k := by omega
  rw [hs,Source284EraseMarkedHistory.marks_add]
  rfl

end Shared.Beeping.NPcoNP.Source284PolynomialMarkedCleanup
