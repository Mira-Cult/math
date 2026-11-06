import Shared.Beeping.NPcoNP.Source284PositivePolynomialTwoSided

/-! Executable arithmetic decoding of the certificate retained behind the
polynomial-workspace construction. This is a mathematical decoder, not yet
a paid finite-table adapter. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284PolynomialRunwayRecovery

open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284PayloadLoop (scratch)
open Shared.Beeping.NPcoNP.Source284ProductIteration
open Shared.Beeping.NPcoNP.Source284PositivePolynomialRunway (block)

def unpairBlock (n code : Nat) : Nat := code / 4^n / 4

theorem zerosBlock (n certificate : Nat) :
    pairTape (List.replicate n false) certificate = 4^n*(4*certificate+2) := by
  induction n with
  | zero => simp [pairTape,scratch]
  | succ n ih =>
    simp only [List.replicate_succ, pairTape, scratch, Source284TableEncode.bit] at *
    rw [ih,pow_succ]
    simp
    ring

theorem unpairBlock_pair (n certificate : Nat) :
    unpairBlock n (pairTape (List.replicate n false) certificate) = certificate := by
  rw [zerosBlock]
  unfold unpairBlock
  rw [Nat.mul_div_cancel_left _ (by positivity : 0 < 4^n)]
  omega

/-- Decode the nested blocks in the reverse of their creation order. -/
def unhistory : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, code => code
  | k+1, a, b, code => unpairBlock a (unhistory k b (a*b) code)

theorem unhistory_history (k a b certificate : Nat) :
    unhistory k a b (historyAfter k a b certificate) = certificate := by
  induction k generalizing a b certificate with
  | zero => rfl
  | succ k ih =>
    simp only [historyAfter,unhistory]
    rw [ih,unpairBlock_pair]

def recover (k n left : Nat) : Nat :=
  unhistory k (n+2) (n+2)
    (unpairBlock (outerAfter k (n+2) (n+2)) (left / 4^(block k n+1)))

/-- The entire arbitrary certificate is recoverable from the exact left
half supplied by `Source284PositivePolynomialTwoSided.source_then`. -/
theorem recover_left (k n certificate : Nat) :
    recover k n (4^(block k n+1)*
      pairTape (List.replicate (outerAfter k (n+2) (n+2)) false)
        (historyAfter k (n+2) (n+2) certificate)) = certificate := by
  unfold recover
  rw [Nat.mul_div_cancel_left _ (by positivity : 0 < 4^(block k n+1)),
    unpairBlock_pair,unhistory_history]

/-- This extraction applies to the actual final configuration of the paid
source run, for every certificate and ignored frame suffix. -/
theorem recover_after_source (k states : Nat)
    (continuation : Nat → Bool → Source284TableEncode.Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states)
    (hv : Source284TableRun.Closed states continuation) :
    recover k w.length
      ((Source284Relative.run
        (Source284PositivePolynomialTwoSided.description k states continuation)
        (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate)
        (Source284PositivePolynomialTwoSided.totalCost k w)).left) = certificate := by
  have h := congrArg Source284Relative.Config.left
    (Source284PositivePolynomialTwoSided.source_then k states continuation w certificate suffix 0 hn hv)
  simp only [Nat.add_zero,Source284TableRun.run,Source284TableRun.toSource,
    Source284HardwireTable.shiftConfig] at h
  rw [h]
  exact recover_left k w.length certificate

namespace Fixtures

example : recover 2 0 (4^(block 2 0+1)*
    pairTape (List.replicate (outerAfter 2 2 2) false)
      (historyAfter 2 2 2 37)) = 37 := by decide +kernel

end Fixtures

end Shared.Beeping.NPcoNP.Source284PolynomialRunwayRecovery
