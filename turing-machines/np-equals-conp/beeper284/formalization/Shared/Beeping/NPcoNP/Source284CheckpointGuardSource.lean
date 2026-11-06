import Shared.Beeping.NPcoNP.Source284CheckpointRestored
import Shared.Beeping.NPcoNP.Source284DynamicGuardSource

/-! Connect the checkpointed workspace to the existing dynamic witness
comparator. All seek and unary-conversion transitions are charged. This
provides an input-side runway; serializer witness-side space is separate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284CheckpointGuardSource

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource)

def description (k r states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284CheckpointRestored.description k r (2+(6+states))
    (Source284GapUnarySource.seek (Source284GapUnaryPrepare.table continuation))

def stream (k r : Nat) (w : List Bool) (suffix : Nat) : Nat :=
  flipped (w++[false]) (Source284CheckpointWorkspace.retained k r w.length suffix/2)

def otherHalf (k r : Nat) (w : List Bool) (suffix : Nat) : Nat :=
  Source284GapUnaryPrepare.retained (Source284GapUnarySource.gap k w.length) (stream k r w suffix)

def totalCost (k r : Nat) (w : List Bool) : Nat :=
  Source284CheckpointRestored.totalCost k r w+3*Source284GapUnarySource.gap k w.length+6

/-- The checkpoint-based initializer supplies the same unary cutoff as the
existing dynamic guard, with its own independently grown input-side suffix. -/
theorem source_then (k r states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k r states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost k r w+fuel) =
    toSource (shiftConfig (1341+317*k+317*r) (run continuation
      ⟨pairTape (List.replicate (Source284DynamicGuardSource.bound k w.length) false)
        (otherHalf k r w suffix),certificate,some 0⟩ fuel)) := by
  have hp := Source284GapUnaryPrepare.closed states continuation hn hv
  have hs := Source284GapUnarySource.seek_closed (6+states)
    (Source284GapUnaryPrepare.table continuation) (by omega) hp
  have h := Source284CheckpointRestored.source_then k r (2+(6+states))
    (Source284GapUnarySource.seek (Source284GapUnaryPrepare.table continuation)) w certificate suffix
    (Source284GapUnarySource.gap k w.length+2+
      (2*Source284GapUnarySource.gap k w.length+4+fuel)) (by omega) hs
  have ht : totalCost k r w+fuel = Source284CheckpointRestored.totalCost k r w+
      (Source284GapUnarySource.gap k w.length+2+
        (2*Source284GapUnarySource.gap k w.length+4+fuel)) := by simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284CheckpointRestored.description k r _
    (Source284GapUnarySource.seek (Source284GapUnaryPrepare.table continuation))) _ _ = _
  rw [h]
  change toSource (shiftConfig (1333+317*k+317*r)
    (run (Source284GapUnarySource.seek (Source284GapUnaryPrepare.table continuation))
      ⟨2^(Source284GapUnarySource.gap k w.length)*(2*certificate+1),2*stream k r w suffix,some 0⟩ _)) = _
  rw [Source284GapUnarySource.seek_then,Source284GapUnaryPrepare.prepare_then]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have he : (1333+317*k+317*r)+2+6 = 1341+317*k+317*r := by omega
  rw [he]
  rfl

noncomputable def costPolynomial (k r : Nat) : Polynomial Nat :=
  Source284CheckpointRestored.costPolynomial k r+
    3*(Source284RestoredPolynomialRunway.countPolynomial k+1)+6

theorem cost_polynomial (k r : Nat) (w : List Bool) :
    totalCost k r w ≤ (costPolynomial k r).eval w.length := by
  have h := Source284CheckpointRestored.totalCost_polynomial k r w
  simp only [totalCost,Source284GapUnarySource.gap,costPolynomial,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_one,Polynomial.eval_ofNat,
    Source284RestoredPolynomialRunway.countPolynomial_eval]
  omega

end Shared.Beeping.NPcoNP.Source284CheckpointGuardSource
