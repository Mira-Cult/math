import Shared.Beeping.NPcoNP.Source284LengthGrowRawContinue

/-! Generate two separately delimited copies of the input-length unary token
block. The outer block remains behind the inner block's sentinel. This is
preparation for a paid stopping counter, not the stopping mechanism itself. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284DoubleLengthTokens

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284LengthGrowLoop (totalTime quarters)
open Shared.Beeping.NPcoNP.Source284LengthGrowSource (setupCost)

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284LengthGrowRawContinue.description (147+states)
    (Source284LengthGrowRawContinue.setup continuation)

def totalCost (w : List Bool) : Nat :=
  Source284LengthGrowSource.totalCost w + (setupCost w + totalTime [] w)

def retained (n suffix : Nat) : Nat :=
  quarters n (((quarters n ((((suffix/4)/4)/2)/2))/2)/2)

/-- Two charged length-generation passes preserve both unary blocks and the
whole arbitrary certificate, and then run the supplied continuation. -/
theorem source_then (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) (totalCost w+fuel) =
    toSource (shiftConfig 449 (run continuation
      ⟨pairTape (List.replicate w.length false) (pairTape (List.replicate w.length false) certificate),
        2*flipped (w++[false]) (retained w.length suffix),some 0⟩ fuel)) := by
  have hs := Source284LengthGrowRawContinue.setup_closed states continuation hn hv
  have hp := Source284LengthGrowRawContinue.source_produce_then (147+states)
    (Source284LengthGrowRawContinue.setup continuation) w certificate suffix
    (setupCost w+(totalTime [] w+fuel)) (by omega) hs
  have ht : totalCost w+fuel = Source284LengthGrowSource.totalCost w +
      (setupCost w+(totalTime [] w+fuel)) := by simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284LengthGrowRawContinue.description (147+states)
    (Source284LengthGrowRawContinue.setup continuation))
    (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) _ = _
  rw [hp,Source284LengthGrowRawContinue.setup_then,Source284SourceRelocation.shiftConfig_add]
  rfl

theorem totalCost_formula (w : List Bool) :
    3*totalCost w = 8*w.length^3 + 162*w.length^2 + 574*w.length+456 := by
  have h1 := Source284LengthGrowSource.totalCost_formula w
  have h2 := Source284LengthGrowTime.zero_formula w
  rw [totalCost]
  simp [setupCost]
  nlinarith

end Shared.Beeping.NPcoNP.Source284DoubleLengthTokens
