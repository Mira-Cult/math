import Shared.Beeping.NPcoNP.NativeHalfMaximalIteration
import Shared.Beeping.NPcoNP.NativeHalfExceptionalCycle

/-! The maximal regular run followed by the literal exceptional cycle,
for an even prepared right-block size. Cleanup in state 18, selector
return and reachability from blank start remain separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeHalfEvenIterations
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.NativeHalfLoopLayout
open Shared.Beeping.NPcoNP.NativeHalfRegularIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopIteration
open Shared.Beeping.NPcoNP.NativeHalfMaximalIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopArithmetic
open Shared.Beeping.NPcoNP.NativeHalfExceptionalCycle
open Shared.Beeping.NPcoNP.UnarySuffixShift

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

lemma encode_one (xs : List Nat) :
    UnaryBank.encode (1::xs) = true :: true :: false :: UnaryBank.encode xs := by
  simp [UnaryBank.encode, UnaryBank.block]

/-- After the final regular cycle, a two-one residual is the actual tape
expected by the exceptional cycle, including its new zero reserve. -/
theorem residual_two_layout (base : Int → Bool) (h : Int) (xs : List Nat) :
    after base h (UnaryBank.encode (1::xs)) =
      prior (put base h true) h (false :: UnaryBank.encode (xs ++ [0])) := by
  rw [encode_one, UnaryBank.append_zero_block]
  simpa using shifted_to_prior base h (false :: UnaryBank.encode xs)

/-- For even `m ≥ 3`, execute every regular cycle and the following
exceptional cycle, reaching the old decrement scanner in state 18. The
whole final tape and exact silent-segment duration are explicit. -/
theorem even_to_scanner (base : Int → Bool) (b : Int) (m : Nat)
    (xs : List Nat) (hb : base b = true) (hm : 3 ≤ m) (heven : m % 2 = 0) :
    let k := regularCount m - 1
    let h := boundary b k + 1
    let bs := bases base b k
    let vs := tailValues xs k ++ [0]
    silentSegment machine
      (cfg 30 (boundary b 0)
        (prior (bases base b 0) (boundary b 0) (suffix (value m) (tailValues xs) 0)))
      (cfg 18 (h+2) (after (put bs h true) (h+1) (false :: UnaryBank.encode vs)))
      (totalDuration (value m) (tailValues xs) k + duration (value m) (tailValues xs) k +
        (2 * (false :: UnaryBank.encode vs).length + 6)) := by
  dsimp only
  let k := regularCount m - 1
  let h := boundary b k + 1
  let bs := bases base b k
  let vs := tailValues xs k
  have hc : 0 < regularCount m := (count_positive_iff m).2 hm
  have hr : m - 2 * regularCount m = 2 := (terminal_two_iff m).2 ⟨by omega, heven⟩
  have hv : value m k = 1 := by simp only [value, k]; omega
  have hs := maximal_iterations base b m xs hb hm
  dsimp only at hs
  change silentSegment machine
      (cfg 30 (boundary b 0)
        (prior (bases base b 0) (boundary b 0) (suffix (value m) (tailValues xs) 0)))
      (cfg 30 h (after bs h (UnaryBank.encode (value m k :: vs))))
      (totalDuration (value m) (tailValues xs) k + duration (value m) (tailValues xs) k) at hs
  rw [hv, residual_two_layout] at hs
  have he := exceptional_cycle (put bs h true) h (vs ++ [0]) (by simp [put])
  exact segAdd machine _ _ _ _ _ hs he

end Shared.Beeping.NPcoNP.NativeHalfEvenIterations
