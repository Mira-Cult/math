import Shared.Beeping.NPcoNP.Source284FlippedScaledQuadratic
import Shared.Beeping.NPcoNP.Source284RawScaledQuadratic

/-! A compile-time fixed coefficient of quadratic blank workspace on both
sides of the protected input frame. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284TwoSidedScaledQuadratic

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284RawScaledQuadratic.description k (354+110*k+states) (Source284FlippedScaledQuadratic.table k continuation)

def totalCost (k : Nat) (w : List Bool) : Nat :=
  Source284RawScaledQuadratic.totalCost k w+Source284FlippedScaledQuadratic.cost k w

def finalTail (k n suffix : Nat) : Nat :=
  halves (k*(n*n)) (Source284FlippedScaledQuadratic.nextTail n
    (Source284RawScaledQuadratic.retained k n suffix)/2)

/-- The code fixes k before any input is read. Its single encoded source
program produces `k*n^2+1` zero bits on each side of the protected frame. -/
theorem source_then (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) (totalCost k w+fuel) =
    toSource (shiftConfig (840+220*k) (run continuation
      ⟨4^(w.length+1)*(4^(w.length+1)*
          (2^(k*(w.length*w.length)+1)*pairTape (List.replicate w.length false)
            (pairTape (List.replicate w.length false) certificate))),
        2*flipped (w++[false]) (2^(k*(w.length*w.length)+1)*finalTail k w.length suffix),some 0⟩ fuel)) := by
  have hc := Source284FlippedScaledQuadratic.closed k states continuation hn hv
  have hp := Source284RawScaledQuadratic.source_then k (354+110*k+states)
    (Source284FlippedScaledQuadratic.table k continuation) w certificate suffix
    (Source284FlippedScaledQuadratic.cost k w+fuel) (by omega) hc
  have ht : totalCost k w+fuel = Source284RawScaledQuadratic.totalCost k w+
      (Source284FlippedScaledQuadratic.cost k w+fuel) := by simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284RawScaledQuadratic.description k (354+110*k+states)
    (Source284FlippedScaledQuadratic.table k continuation))
    (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) _ = _
  rw [hp,Source284FlippedScaledQuadratic.prepare_then,Source284SourceRelocation.shiftConfig_add]
  have he : 486+110*k+(354+110*k)=840+220*k := by omega
  rw [he]
  rfl

theorem totalCost_formula (k : Nat) (w : List Bool) :
    3*totalCost k w = 6*k*k*w.length^4+(16+48*k)*w.length^3+
      (318+273*k)*w.length^2+(1154+264*k)*w.length+1053+156*k := by
  have h1 := Source284DoubleLengthTokens.totalCost_formula w
  have h2 := Source284LengthGrowTime.zero_formula w
  have h3 := Source284SquareRepeatCost.repeatCost_formula k w.length 0 (w.length+1)
  unfold totalCost Source284RawScaledQuadratic.totalCost Source284RawSquareRepeat.totalCost
    Source284FlippedScaledQuadratic.cost Source284LengthGrowSource.setupCost
  simp only [List.length_append,List.length_singleton,mul_zero,add_zero] at *
  nlinarith

end Shared.Beeping.NPcoNP.Source284TwoSidedScaledQuadratic
