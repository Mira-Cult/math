import Shared.Beeping.NPcoNP.NativeHalfOddResidual

/-! Composition of the prepared maximal regular HALF loop and its
residual-one dispatch. State 37's cleanup, the selector ABI, and initial
reachability are separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeHalfOddComposition
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.NativeHalfRegularIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
open Shared.Beeping.NPcoNP.NativeHalfMaximalIteration
open Shared.Beeping.NPcoNP.NativeHalfOddResidual
open Shared.Beeping.NPcoNP.UnarySuffixShift

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem final_value_odd (m : Nat) (hm : 3 ≤ m) (hodd : m % 2 = 1) :
    value m (regularCount m - 1) = 0 := by
  have hc : 0 < regularCount m := (count_positive_iff m).2 hm
  have ht : m - 2 * regularCount m = 1 := (terminal_one_iff m).2 hodd
  simp only [value]
  omega

/-- For a supplied prepared boundary with an odd right-block length `m ≥ 3`,
the literal table completes all regular cycles and then takes three silent
steps to state 37. The entire resulting tape and elapsed time are explicit. -/
theorem maximal_odd_to_state37 (base : Int → Bool) (b : Int) (m : Nat)
    (xs : List Nat) (hb : base b = true) (hm : 3 ≤ m) (hodd : m % 2 = 1) :
    let k := regularCount m - 1
    let g := boundary b k + 1
    let t := after (bases base b k) g (UnaryBank.encode (0 :: tailValues xs k))
    silentSegment machine
      (cfg 30 (boundary b 0)
        (prior (bases base b 0) (boundary b 0) (suffix (value m) (tailValues xs) 0)))
      (cfg 37 (g+3) (put (put (put t g true) (g+1) false) (g+2) false))
      (totalDuration (value m) (tailValues xs) k + duration (value m) (tailValues xs) k + 3) := by
  dsimp only
  let k := regularCount m - 1
  let g := boundary b k + 1
  let t := after (bases base b k) g (UnaryBank.encode (0 :: tailValues xs k))
  have h := maximal_iterations base b m xs hb hm
  dsimp only at h
  have hval : value m k = 0 := final_value_odd m hm hodd
  have h' : silentSegment machine
      (cfg 30 (boundary b 0)
        (prior (bases base b 0) (boundary b 0) (suffix (value m) (tailValues xs) 0)))
      (cfg 30 g t)
      (totalDuration (value m) (tailValues xs) k + duration (value m) (tailValues xs) k) := by
    simpa [k, g, t, suffix, hval] using h
  have hn := residual_one_step (bases base b k) g (tailValues xs k)
  exact segAdd machine _ _ _ _ _ h' hn

end Shared.Beeping.NPcoNP.NativeHalfOddComposition
