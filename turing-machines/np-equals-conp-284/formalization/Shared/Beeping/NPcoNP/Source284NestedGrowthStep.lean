import Shared.Beeping.NPcoNP.Source284NestedBranchSource
import Shared.Beeping.NPcoNP.Source284ReusableTokenRound

/-! One finite source table marks one outer token and transfers the entire
inner block into the suffix counter, then enters a supplied continuation.
The exhaustion entry is not yet connected to a suitable continuation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284NestedGrowthStep

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284NestedBranchDispatch.table (Source284ReusableTokenRound.table continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (85+states) (table continuation) := by
  have hg := Source284ReusableTokenRound.closed states continuation hn hv
  have hb := Source284NestedBranchSource.closed (42+states) (Source284ReusableTokenRound.table continuation) (by omega) hg
  have he : 43+(42+states) = 85+states := by omega
  rw [he] at hb
  exact hb

def cost (m k n width : Nat) : Nat :=
  4*m+4*k+14+Source284ReusableTokenRound.roundCost m n width

/-- One outer token is marked, then its inner block adds `m` counter marks;
the output blocks and the entire high certificate are restored. -/
theorem growth_then (continuation : Nat → Bool → Row) (m k n : Nat)
    (rest w : List Bool) (certificate higher fuel : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ false::rest) certificate),
        2*flipped w (counter n higher),some 0⟩ (cost m k n w.length+fuel) =
    shiftConfig 85 (run continuation
      ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ true::rest) certificate),
        2*flipped w (counter (n+m) (halves m higher)),some 0⟩ fuel) := by
  have ht : cost m k n w.length+fuel =
      (4*m+4*k+14)+(Source284ReusableTokenRound.roundCost m n w.length+fuel) := by simp [cost]; omega
  rw [ht]
  unfold table
  rw [Source284NestedBranchDispatch.mark_then,Source284ReusableTokenRound.round_then,
    Source284SourceRelocation.shiftConfig_add]

theorem cost_formula (m k n width : Nat) :
    cost m k n width = 3*m*m+m*(2*n+4*width+33)+4*k+30 := by
  rw [cost,Source284ReusableTokenRound.roundCost_formula]
  ring

end Shared.Beeping.NPcoNP.Source284NestedGrowthStep
