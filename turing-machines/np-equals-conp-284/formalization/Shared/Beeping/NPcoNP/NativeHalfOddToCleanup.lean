import Shared.Beeping.NPcoNP.NativeHalfOddComposition
import Shared.Beeping.NPcoNP.NativeHalfOddCleanupLayout

/-! Compose odd residuals and the maximal odd HALF loop with their literal
cleanup. These are prepared boundaries; the entry and selector return are
separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeHalfOddToCleanup

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.NativeHalfRegularIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
open Shared.Beeping.NPcoNP.NativeHalfOddResidual
open Shared.Beeping.NPcoNP.NativeHalfOddComposition
open Shared.Beeping.NPcoNP.NativeHalfOddCleanupLayout
open Shared.Beeping.NPcoNP.NativeHalfOddCleanupComposed
open Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
open Shared.Beeping.NPcoNP.UnarySuffixShift

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

theorem residual_one_written_tape (base : Int → Bool) (g : Int) (xs : List Nat) :
    let t := after base g (UnaryBank.encode (0::xs))
    put (put (put t g true) (g+1) false) (g+2) false =
      after (put base g true) (g+1) (false :: UnaryBank.encode xs) := by
  dsimp only
  have he : UnaryBank.encode (0::xs)=true :: false :: UnaryBank.encode xs := by
    simp [UnaryBank.encode,UnaryBank.block]
  rw [he]
  exact odd_writes base g (UnaryBank.encode xs)

/-- The one-unit odd residual passes through cleanup to state 25, with
the complete tape and exact positive duration. -/
theorem residual_one_through_cleanup (base : Int → Bool) (g : Int) (xs : List Nat) :
    silentSegment machine (cfg 30 g (after base g (UnaryBank.encode (0::xs))))
      (cfg 25 g (postTape (put base g true) g xs))
      (2*(UnaryBank.encode xs).length+10) := by
  have h := residual_one_step base g xs
  dsimp only at h
  rw [residual_one_written_tape] at h
  have hc := odd_cleanup (put base g true) g xs
  have hall := segAdd machine _ _ _ 3 (2*(UnaryBank.encode xs).length+7) h hc
  convert hall using 1 <;> omega

/-- For every supplied odd right-block size at least three, all regular
iterations, the residual dispatch, and both cleanup scans complete silently
to state 25. The final tape and total duration are explicit. -/
theorem maximal_odd_through_cleanup (base : Int → Bool) (b : Int) (m : Nat)
    (xs : List Nat) (hb : base b=true) (hm : 3≤m) (hodd : m%2=1) :
    let k := regularCount m-1
    let g := boundary b k+1
    let bs := bases base b k
    let vs := tailValues xs k
    silentSegment machine
      (cfg 30 (boundary b 0)
        (prior (bases base b 0) (boundary b 0) (suffix (value m) (tailValues xs) 0)))
      (cfg 25 g (postTape (put bs g true) g vs))
      (totalDuration (value m) (tailValues xs) k + duration (value m) (tailValues xs) k +
        3 + (2*(UnaryBank.encode vs).length+7)) := by
  dsimp only
  let k := regularCount m-1
  let g := boundary b k+1
  let bs := bases base b k
  let vs := tailValues xs k
  have h := maximal_odd_to_state37 base b m xs hb hm hodd
  dsimp only at h
  change silentSegment machine _
    (cfg 37 (g+3) (put (put (put (after bs g (UnaryBank.encode (0::vs))) g true)
      (g+1) false) (g+2) false)) _ at h
  rw [residual_one_written_tape] at h
  have hc := odd_cleanup (put bs g true) g vs
  exact segAdd machine _ _ _ _ _ h hc

end Shared.Beeping.NPcoNP.NativeHalfOddToCleanup

#print axioms Shared.Beeping.NPcoNP.NativeHalfOddToCleanup.residual_one_through_cleanup
#print axioms Shared.Beeping.NPcoNP.NativeHalfOddToCleanup.maximal_odd_through_cleanup
