import Shared.Beeping.NPcoNP.Source284PadTokenBlock
import Shared.Beeping.NPcoNP.Source284DoubleLengthTokens

/-! Raw input initializes two separately delimited token blocks of length
`n+2`, including when the parsed input length is zero or one. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284DoublePositiveTokens

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284LengthGrowLoop (totalTime quarters)
open Shared.Beeping.NPcoNP.Source284LengthGrowSource (setupCost)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

def middle (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ScratchShiftCycle.repeatTable 4
    (Source284LengthGrowRawContinue.setup (Source284ScratchShiftCycle.repeatTable 4 continuation))

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284LengthGrowRawContinue.description (56+(147+(56+states))) (middle continuation)

def padCost (w : List Bool) : Nat := 4*(4*(w++[false]).length+7)

def totalCost (w : List Bool) : Nat := Source284DoubleLengthTokens.totalCost w+2*padCost w

def retained (n suffix : Nat) : Nat :=
  (quarters n (((quarters n ((((suffix/4)/4)/2)/2)/2^4)/2)/2))/2^4

theorem middle_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (56+(147+(56+states))) (middle continuation) := by
  have hp := Source284ScratchShiftCycle.repeat_closed 4 states continuation hn hv
  have hs := Source284LengthGrowRawContinue.setup_closed (56+states)
    (Source284ScratchShiftCycle.repeatTable 4 continuation) (by omega) (by simpa using hp)
  have hq := Source284ScratchShiftCycle.repeat_closed 4 (147+(56+states))
    (Source284LengthGrowRawContinue.setup (Source284ScratchShiftCycle.repeatTable 4 continuation)) (by omega) hs
  simpa [middle] using hq

/-- Both padded blocks are constructed and each shift is paid in the same
fixed finite source table; the arbitrary certificate is retained. -/
theorem source_then (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost w+fuel) =
    toSource (shiftConfig 561 (run continuation
      ⟨pairTape (List.replicate (w.length+2) false) (pairTape (List.replicate (w.length+2) false) certificate),
        2*flipped (w++[false]) (retained w.length suffix),some 0⟩ fuel)) := by
  have hp := Source284LengthGrowRawContinue.source_produce_then (56+(147+(56+states)))
    (middle continuation) w certificate suffix
    (padCost w+(setupCost w+(totalTime [] w+(padCost w+fuel))))
    (by omega) (middle_closed states continuation hn hv)
  have ht : totalCost w+fuel = Source284LengthGrowSource.totalCost w+
      (padCost w+(setupCost w+(totalTime [] w+(padCost w+fuel)))) := by
    simp [totalCost,Source284DoubleLengthTokens.totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284LengthGrowRawContinue.description (56+(147+(56+states)))
    (middle continuation)) _ _ = _
  rw [hp]
  unfold middle padCost
  rw [Source284PadTokenBlock.pad_then,Source284LengthGrowRawContinue.setup_then,
    Source284PadTokenBlock.pad_then]
  simp only [Source284SourceRelocation.shiftConfig_add]
  rfl

noncomputable def costPolynomial : Polynomial Nat :=
  8*Polynomial.X^3+162*Polynomial.X^2+574*Polynomial.X+456+
    2*(4*(4*(Polynomial.X+1)+7))

theorem totalCost_polynomial (w : List Bool) : totalCost w ≤ costPolynomial.eval w.length := by
  have h := Source284DoubleLengthTokens.totalCost_formula w
  unfold totalCost padCost
  simp only [List.length_append,List.length_singleton,costPolynomial,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

end Shared.Beeping.NPcoNP.Source284DoublePositiveTokens
