import Shared.Beeping.NPcoNP.Source284InitialCertificateSentinel
import Shared.Beeping.NPcoNP.Source284DoublePositiveTokens

/-! Install a certificate delimiter before creating both positive-length
unary blocks. The delimiter remains immediately above the original arbitrary
certificate, underneath both blocks. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284SentinelPositiveTokens

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284LengthGrowLoop (totalTime quarters)
open Shared.Beeping.NPcoNP.Source284LengthGrowSource (setupCost)
open Shared.Beeping.NPcoNP.Source284DoublePositiveTokens (padCost)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284LengthGrowRawContinue.setup (Source284DoublePositiveTokens.middle continuation)

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284InitialCertificateSentinel.description (406+states) (table continuation)

def totalCost (w : List Bool) : Nat :=
  Source284InitialCertificateSentinel.totalCost w+
    (setupCost w+totalTime [] w)+(padCost w+(setupCost w+totalTime [] w)+padCost w)

def retained (n suffix : Nat) : Nat :=
  let raw := (((suffix/4)/4)/2)
  let first := quarters n ((raw/2)/2)
  let middle := first/2^4
  (quarters n ((middle/2)/2))/2^4

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (406+states) (table continuation) := by
  have hm := Source284DoublePositiveTokens.middle_closed states continuation hn hv
  have hs := Source284LengthGrowRawContinue.setup_closed (56+(147+(56+states)))
    (Source284DoublePositiveTokens.middle continuation) (by omega) hm
  simpa [table,show 147+(56+(147+(56+states)))=406+states by omega] using hs

/-- Both token blocks are paid for after the actual startup marker. -/
theorem source_then (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate)
      (totalCost w+fuel) =
    toSource (shiftConfig 575 (run continuation
      ⟨pairTape (List.replicate (w.length+2) false)
          (pairTape (List.replicate (w.length+2) false) (2*certificate+1)),
        2*flipped (w++[false]) (retained w.length suffix),some 0⟩ fuel)) := by
  have hc := closed states continuation hn hv
  have h := Source284InitialCertificateSentinel.source_then (406+states) (table continuation)
    w certificate suffix ((setupCost w+totalTime [] w)+
      (padCost w+(setupCost w+totalTime [] w)+(padCost w+fuel))) (by omega) hc
  have ht : totalCost w+fuel = Source284InitialCertificateSentinel.totalCost w+
      ((setupCost w+totalTime [] w)+(padCost w+(setupCost w+totalTime [] w)+(padCost w+fuel))) := by
    simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284InitialCertificateSentinel.description (406+states)
    (table continuation)) _ _ = _
  rw [h]
  unfold table
  have ht2 : (setupCost w+totalTime [] w)+(padCost w+(setupCost w+totalTime [] w)+(padCost w+fuel)) =
      setupCost w+(totalTime [] w+(padCost w+(setupCost w+(totalTime [] w+(padCost w+fuel))))) := by omega
  rw [ht2]
  rw [Source284LengthGrowRawContinue.setup_then]
  unfold Source284DoublePositiveTokens.middle padCost
  rw [Source284PadTokenBlock.pad_then,Source284LengthGrowRawContinue.setup_then,
    Source284PadTokenBlock.pad_then]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  rfl

noncomputable def costPolynomial : Polynomial Nat :=
  Source284DoublePositiveTokens.costPolynomial+(4*(Polynomial.X+1)+7)

theorem totalCost_polynomial (w : List Bool) : totalCost w ≤ costPolynomial.eval w.length := by
  have h := Source284DoublePositiveTokens.totalCost_polynomial w
  have he : totalCost w = Source284DoublePositiveTokens.totalCost w+(4*(w++[false]).length+7) := by
    simp [totalCost,Source284InitialCertificateSentinel.totalCost,
      Source284DoublePositiveTokens.totalCost,Source284DoubleLengthTokens.totalCost,
      Source284LengthGrowSource.totalCost]; omega
  rw [he]
  simp [costPolynomial,Polynomial.eval_add,Polynomial.eval_mul] at *
  omega

end Shared.Beeping.NPcoNP.Source284SentinelPositiveTokens
