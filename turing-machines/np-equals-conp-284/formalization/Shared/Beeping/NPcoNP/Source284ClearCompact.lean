import Shared.Beeping.NPcoNP.Source284SentinelClear

/-! Clear one known boundary sentinel and compact an adjacent zero gap,
stopping at the next actual sentinel. No gap count is supplied to the table. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284ClearCompact

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284SentinelClear.table (Source284ScratchCompactLoop.table continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (18+states) (table continuation) := by
  have h := Source284SentinelClear.closed (14+states) (Source284ScratchCompactLoop.table continuation)
    (by omega) (Source284ScratchCompactLoop.closed states continuation hn hv)
  change Closed (4+(14+states)) (table continuation) at h
  convert h using 1 <;> omega

def cost (count : Nat) (w : List Bool) := 4+(count+1)*(8*w.length+11)

theorem cross_then (continuation : Nat → Bool → Row) (count : Nat) (w : List Bool)
    (input tail fuel : Nat) :
    run (table continuation)
      ⟨2^(count+1)*(2*input+1)+1,2*flipped w tail,some 0⟩ (cost count w+fuel) =
    shiftConfig 18 (run continuation
      ⟨2*input+1,2*flipped w (2^(count+1)*tail),some 0⟩ fuel) := by
  have hl : 2^(count+1)*(2*input+1)+1 = 2*(2^count*(2*input+1))+1 := by
    rw [pow_succ]; ring
  have ht : cost count w+fuel = 4+((count+1)*(8*w.length+11)+fuel) := by simp [cost]; omega
  rw [hl,ht]
  unfold table
  rw [Source284SentinelClear.clear_then]
  have he : 2*(2^count*(2*input+1)) = 2^(count+1)*(2*input+1) := by rw [pow_succ]; ring
  rw [he,Source284ScratchCompactLoop.countdown_after,Source284SourceRelocation.shiftConfig_add]

end Shared.Beeping.NPcoNP.Source284ClearCompact
