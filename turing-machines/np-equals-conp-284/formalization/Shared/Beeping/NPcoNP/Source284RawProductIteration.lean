import Shared.Beeping.NPcoNP.Source284ProductGrowth
import Shared.Beeping.NPcoNP.Source284DoubleLengthTokens

/-! A fixed finite source table initializes two input-length token blocks
from the raw frame and executes a fixed number of paid product-and-recycle
stages. It preserves the arbitrary certificate and tracks the ignored suffix. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284RawProductIteration

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ProductIteration

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284DoubleLengthTokens.description (287*k+states) (table k continuation)

def totalCost (k : Nat) (w : List Bool) : Nat :=
  Source284DoubleLengthTokens.totalCost w+cost k w.length w.length (w++[false]).length

/-- All power stages are part of one fixed source description. The stages
never receive a preloaded input-length or power counter. -/
theorem source_then (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost k w+fuel) =
    toSource (shiftConfig (449+287*k) (run continuation
      ⟨pairTape (List.replicate (innerAfter k w.length w.length) false)
          (pairTape (List.replicate (outerAfter k w.length w.length) false)
            (historyAfter k w.length w.length certificate)),
        2*flipped (w++[false]) (suffixAfter k w.length w.length
          (Source284DoubleLengthTokens.retained w.length suffix)),some 0⟩ fuel)) := by
  have hc := closed k states continuation hn hv
  have hp := Source284DoubleLengthTokens.source_then (287*k+states) (table k continuation)
    w certificate suffix (cost k w.length w.length (w++[false]).length+fuel) (by omega) hc
  have ht : totalCost k w+fuel = Source284DoubleLengthTokens.totalCost w+
      (cost k w.length w.length (w++[false]).length+fuel) := by simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284DoubleLengthTokens.description (287*k+states) (table k continuation)) _ _ = _
  rw [hp,iterate_then,Source284SourceRelocation.shiftConfig_add]

theorem source_all_inputs_then (k states : Nat) (continuation : Nat → Bool → Row)
    (input certificate fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description k states continuation) (Source284Relative.initial input certificate)
        (totalCost k w+fuel) = toSource (shiftConfig (449+287*k) (run continuation
          ⟨pairTape (List.replicate (innerAfter k w.length w.length) false)
              (pairTape (List.replicate (outerAfter k w.length w.length) false)
                (historyAfter k w.length w.length certificate)),
            2*flipped (w++[false]) (suffixAfter k w.length w.length
              (Source284DoubleLengthTokens.retained w.length suffix)),some 0⟩ fuel)) := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [← hw]
  exact source_then k states continuation w certificate suffix fuel hn hv

noncomputable def costPolynomial (k : Nat) : Polynomial Nat :=
  8*Polynomial.X^3+162*Polynomial.X^2+574*Polynomial.X+456+
    Source284ProductIteration.costPolynomial k Polynomial.X Polynomial.X (Polynomial.X+1)

/-- For each fixed stage count, the total source initialization time is
bounded by one explicit polynomial in parsed payload length. -/
theorem totalCost_polynomial (k : Nat) (w : List Bool) : totalCost k w ≤ (costPolynomial k).eval w.length := by
  have hinit := Source284DoubleLengthTokens.totalCost_formula w
  have hstages := Source284ProductIteration.cost_polynomial k w.length w.length w.length
    (w++[false]).length Polynomial.X Polynomial.X (Polynomial.X+1)
    (by simp) (by simp) (by simp)
  unfold totalCost
  simp only [costPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_ofNat]
  omega

end Shared.Beeping.NPcoNP.Source284RawProductIteration
