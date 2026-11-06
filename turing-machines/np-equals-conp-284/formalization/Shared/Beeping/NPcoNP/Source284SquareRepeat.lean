import Shared.Beeping.NPcoNP.Source284NestedReset
import Shared.Beeping.NPcoNP.Source284SquareLoopSource
import Shared.Beeping.NPcoNP.Source284ReusableTokenIterations

/-! A compile-time fixed number of autonomous square-growth passes. The
outer token block is reset after each pass; the current suffix counter and
arbitrary certificate are preserved. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284SquareRepeat

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)
open Shared.Beeping.NPcoNP.Source284SquareLoopTotal (loopCost)

def round (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284SquareLoop.table (Source284NestedReset.table (Source284NestedReturn.table continuation))

theorem round_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (110+states) (round continuation) := by
  have h1 := Source284NestedReturn.closed states continuation hn hv
  have h2 := Source284NestedReset.closed (10+states) (Source284NestedReturn.table continuation) (by omega) h1
  have h3 := Source284SquareLoopSource.closed (12+(10+states))
    (Source284NestedReset.table (Source284NestedReturn.table continuation)) (by omega) h2
  have he : 88+(12+(10+states))=110+states := by omega
  rw [he] at h3
  exact h3

def roundCost (n current width : Nat) : Nat := loopCost n n 0 current width+(8*n+12)

/-- One pass adds `n^2` counter marks, then restores both token blocks. -/
theorem round_then (continuation : Nat → Bool → Row) (n current : Nat) (w : List Bool)
    (certificate higher fuel : Nat) :
    run (round continuation)
      ⟨pairTape (List.replicate n false) (pairTape (List.replicate n false) certificate),
        2*flipped w (counter current higher),some 0⟩ (roundCost n current w.length+fuel) =
    shiftConfig 110 (run continuation
      ⟨pairTape (List.replicate n false) (pairTape (List.replicate n false) certificate),
        2*flipped w (counter (current+n*n) (halves (n*n) higher)),some 0⟩ fuel) := by
  have ht : roundCost n current w.length+fuel =
      loopCost n n 0 current w.length+((4*n+4*(List.replicate n true).length+12)+fuel) := by
    simp [roundCost]; omega
  rw [ht]
  unfold round
  have hl := Source284SquareLoopTotal.loop_then
    (Source284NestedReset.table (Source284NestedReturn.table continuation)) n n 0 current w certificate higher
    ((4*n+4*(List.replicate n true).length+12)+fuel)
  simp only [List.replicate_zero,List.nil_append,Nat.zero_add] at hl
  rw [hl,Source284NestedReset.reset_then]
  simp only [List.length_replicate]
  rw [Source284SourceRelocation.shiftConfig_add]

def repeatTable : Nat → (Nat → Bool → Row) → (Nat → Bool → Row)
  | 0, continuation => continuation
  | k+1, continuation => round (repeatTable k continuation)

theorem repeat_closed (k states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (110*k+states) (repeatTable k continuation) := by
  induction k with
  | zero => simpa [repeatTable] using hv
  | succ k ih =>
    have h := round_closed (110*k+states) (repeatTable k continuation) (by omega) ih
    have he : 110+(110*k+states)=110*(k+1)+states := by omega
    rw [he] at h
    exact h

def repeatCost : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | k+1, n, current, width => roundCost n current width + repeatCost k n (current+n*n) width

/-- Every fixed `k` is compiled into one finite source table; the inner
iteration count remains controlled by the tape. -/
theorem repeat_then (k : Nat) (continuation : Nat → Bool → Row) (n current : Nat) (w : List Bool)
    (certificate higher fuel : Nat) :
    run (repeatTable k continuation)
      ⟨pairTape (List.replicate n false) (pairTape (List.replicate n false) certificate),
        2*flipped w (counter current higher),some 0⟩ (repeatCost k n current w.length+fuel) =
    shiftConfig (110*k) (run continuation
      ⟨pairTape (List.replicate n false) (pairTape (List.replicate n false) certificate),
        2*flipped w (counter (current+k*(n*n)) (halves (k*(n*n)) higher)),some 0⟩ fuel) := by
  induction k generalizing current higher with
  | zero => simp [repeatTable,repeatCost,shiftConfig,halves]
  | succ k ih =>
    have ht : repeatCost (k+1) n current w.length+fuel =
        roundCost n current w.length+(repeatCost k n (current+n*n) w.length+fuel) := by simp [repeatCost]; omega
    rw [ht]
    change run (round (repeatTable k continuation)) _ _ = _
    rw [round_then,ih,Source284SourceRelocation.shiftConfig_add,
      Source284ReusableTokenIterations.halves_add]
    have ha : current+n*n+k*(n*n)=current+(k+1)*(n*n) := by ring
    have hb : k*(n*n)+n*n=(k+1)*(n*n) := by ring
    have hc : 110+110*k=110*(k+1) := by omega
    rw [ha,hb,hc]

end Shared.Beeping.NPcoNP.Source284SquareRepeat
