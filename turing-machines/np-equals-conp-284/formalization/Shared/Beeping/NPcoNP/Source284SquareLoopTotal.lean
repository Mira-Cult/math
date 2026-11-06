import Shared.Beeping.NPcoNP.Source284SquareLoop
import Shared.Beeping.NPcoNP.Source284ReusableTokenIterations

/-! Termination and exact polynomial cost of the tape-controlled outer loop.
The mathematical index counts initially unmarked outer tokens; the finite
table detects exhaustion itself. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284SquareLoopTotal

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)

def loopCost : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, m, k, _, _ => 4*m+4*k+14
  | r+1, m, k, n, width => Source284NestedGrowthStep.cost m k n width + loopCost r m (k+1) (n+m) width

/-- The fixed table autonomously processes all `r` remaining outer tokens,
then detects exhaustion and runs its continuation. -/
theorem loop_then (continuation : Nat → Bool → Row) (r m k n : Nat) (w : List Bool)
    (certificate higher fuel : Nat) :
    run (Source284SquareLoop.table continuation)
      ⟨pairTape (List.replicate m false)
        (pairTape (List.replicate k true ++ List.replicate r false) certificate),
        2*flipped w (counter n higher),some 0⟩ (loopCost r m k n w.length+fuel) =
    shiftConfig 88 (run continuation
      ⟨pairTape (List.replicate m false) (pairTape (List.replicate (k+r) true) certificate),
        2*flipped w (counter (n+r*m) (halves (r*m) higher)),some 0⟩ fuel) := by
  induction r generalizing k n higher with
  | zero =>
    simpa [loopCost,halves] using Source284SquareLoop.exhausted_then continuation m k certificate
      (flipped w (counter n higher)) fuel
  | succ r ih =>
    simp only [loopCost,List.replicate_succ]
    rw [show Source284NestedGrowthStep.cost m k n w.length + loopCost r m (k+1) (n+m) w.length + fuel =
      Source284NestedGrowthStep.cost m k n w.length + (loopCost r m (k+1) (n+m) w.length+fuel) by omega,
      Source284ScratchScanner.run_add,Source284SquareLoop.growth]
    have hmarks : List.replicate k true ++ true::List.replicate r false =
        List.replicate (k+1) true ++ List.replicate r false := by
      rw [List.replicate_add]
      simp [List.append_assoc]
    rw [hmarks,ih,Source284ReusableTokenIterations.halves_add]
    have h1 : k+1+r=k+(r+1) := by omega
    have h2 : n+m+r*m=n+(r+1)*m := by ring
    have h3 : r*m+m=(r+1)*m := by ring
    rw [h1,h2,h3]

/-- Exact polynomial source-step cost; no division or truncated
subtraction is used in the identity. -/
theorem loopCost_formula (r m k n width : Nat) :
    loopCost r m k n width+(m*m+2)*r =
      r*(3*m*m+m*(2*n+4*width+33)+4*k+30)+(m*m+2)*r*r+4*m+4*(k+r)+14 := by
  induction r generalizing k n with
  | zero => simp [loopCost]
  | succ r ih =>
    simp only [loopCost,Source284NestedGrowthStep.cost_formula]
    have h := ih (k+1) (n+m)
    nlinarith

end Shared.Beeping.NPcoNP.Source284SquareLoopTotal
