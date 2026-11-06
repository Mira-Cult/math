import Shared.Beeping.NPcoNP.Source284RetryDispatch
import Shared.Beeping.NPcoNP.Source284MatchLoopComplete

/-! An actual finite linked table runs the comparator and, on the
payload-longer outcome, resets both marked sides and adds one unary pair.
This is one paid retry, not yet the loop that repeats it until equality. -/
set_option maxRecDepth 2048
namespace Shared.Beeping.NPcoNP.Source284OneRetry

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284MatchLoop.table (Source284RetryDispatch.table continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 3 ≤ states) (hv : Closed states continuation) : Closed (97+states) (table continuation) := by
  have hd := Source284RetryDispatch.closed states continuation hn hv
  have hm := Source284MatchLoop.closed (49+states) (Source284RetryDispatch.table continuation) (by omega) hd
  have he : 48+(49+states) = 97+states := by omega
  rw [he] at hm
  exact hm

def cost (k n : Nat) : Nat := (4*k*k+20*k+16)+(4*k+12*n+40)

theorem cost_formula (k n : Nat) : cost k n = 4*k*k+24*k+12*n+56 := by
  unfold cost
  ring

/-- If the prepared unary count equals the length of `w` but the payload
continues with `b::rest`, this one source table detects the mismatch, clears
both marker tracks, adds one unary pair and reaches its finite continuation.
Two high-suffix bits are overwritten during the charged growth operation. -/
theorem retry (continuation : Nat → Bool → Row) (w rest : List Bool) (b : Bool)
    (certificate tail : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate w.length false) certificate,
        2*flipped ((w++b::rest)++[false]) tail,some 0⟩
      (cost w.length ((w++b::rest).length)) =
    ⟨pairTape (List.replicate (w.length+1) false) certificate,
      2*flipped ((w++b::rest)++[false]) (tail/4),some 97⟩ := by
  have hlen : (w++b::rest).length = (w++[b]).length+rest.length := by simp; omega
  have ht : cost w.length ((w++b::rest).length) =
      (4*w.length*w.length+20*w.length+16)+
        (4*(List.replicate w.length true).length+12*((w++[b]).length+rest.length)+40) := by
    simp only [List.length_replicate]
    rw [hlen]
    rfl
  rw [ht,run_add]
  unfold table
  rw [Source284MatchLoopComplete.more_payload]
  change run (Source284MatchLoop.table (Source284RetryDispatch.table continuation))
    (shiftConfig 48 ⟨pairTape (List.replicate w.length true) certificate,
      2*zeros (w++[b]) (flipped (rest++[false]) tail),some 1⟩) _ = _
  rw [Source284MatchLoop.relocated_run]
  rw [Source284RetryDispatch.run_retry _ _ _ _ (by omega),Source284MatchGrow.reset_grow]
  simp [shiftConfig,List.append_assoc]

end Shared.Beeping.NPcoNP.Source284OneRetry
