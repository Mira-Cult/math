import Shared.Beeping.NPcoNP.NativeHalfZeroResidual
import Shared.Beeping.NPcoNP.NativeHalfOddResidual
import Shared.Beeping.NPcoNP.NativeHalfEvenIterations
import Shared.Beeping.NPcoNP.NativeHalfOddComposition

/-! Prepared native-HALF loop progress for every finite right-block size.
The input below contains `0`, then `m` ones, a zero delimiter, the encoded
bank `xs`, and a fresh `10` reserve before the zero tail. The prefix is
arbitrary. This theorem ends at cleanup states and does not assert entry
reachability, selector correctness, or full HALF. -/
namespace Shared.Beeping.NPcoNP.NativeHalfAllResiduals
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.NativeHalfLoopLayout
open Shared.Beeping.NPcoNP.NativeHalfRegularIteration
open Shared.Beeping.NPcoNP.NativeHalfLoopIteration
open Shared.Beeping.NPcoNP.NativeHalfEvenIterations
open Shared.Beeping.NPcoNP.NativeHalfOddComposition
open Shared.Beeping.NPcoNP.NativeHalfOddResidual
open Shared.Beeping.NPcoNP.NativeHalfZeroResidual
open Shared.Beeping.NPcoNP.NativeHalfExceptionalCycle
open Shared.Beeping.NPcoNP.UnarySuffixShift

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def prepared (base : Int → Bool) (b : Int) (m : Nat) (xs : List Nat) : Int → Bool :=
  after base b (if m = 0 then false :: UnaryBank.encode xs else UnaryBank.encode ((m-1)::xs))

/-- The single input convention consists of `m` ones and a zero delimiter,
followed by the supplied bank; `after` appends the reserve and zero tail. -/
theorem prepared_shape (base : Int → Bool) (b : Int) (m : Nat) (xs : List Nat) :
    prepared base b m xs =
      after base b (List.replicate m true ++ false :: UnaryBank.encode xs) := by
  cases m with
  | zero => simp [prepared]
  | succ m => simp [prepared, UnaryBank.encode, UnaryBank.block, List.append_assoc]

theorem prepared_zero (base : Int → Bool) (b : Int) (xs : List Nat) :
    prepared base b 0 xs b = false ∧ prepared base b 0 xs (b+1) = false := by
  simp only [prepared]
  constructor
  · exact (gap_cells base b (false :: UnaryBank.encode xs)).2.2
  · have h := after_suffix_bit base b (false :: UnaryBank.encode xs) 0 (by simp)
    simpa [bitAt] using h

theorem prepared_one (base : Int → Bool) (b : Int) (xs : List Nat) :
    prepared base b 1 xs = after base b (UnaryBank.encode (0::xs)) := by
  simp [prepared]

theorem prepared_two (base : Int → Bool) (b : Int) (xs : List Nat) :
    prepared base b 2 xs = prior (put base b true) b (false :: UnaryBank.encode (xs ++ [0])) := by
  simpa [prepared] using residual_two_layout base b xs

theorem prepared_large (base : Int → Bool) (b : Int) (m : Nat) (xs : List Nat) (hm : 3 ≤ m) :
    prepared base b m xs =
      prior (put base b true) b (UnaryBank.encode ((m-3)::(xs ++ [0]))) := by
  have ht := next_cycle_layout base (b-1) (m-3) xs
  have hm' : m - 3 + 2 = m - 1 := by omega
  simpa [prepared, show m ≠ 0 by omega, hm', Int.sub_add_cancel] using ht

/-- Every finite right-block size reaches its branch's cleanup state after
finitely many positive, silent literal-table transitions. `m` is the count
of ones at this supplied boundary, not yet the original register value. -/
theorem all_residuals (base : Int → Bool) (b : Int) (m : Nat) (xs : List Nat) :
    ∃ n : Nat, 0 < n ∧ ∃ h : Int, ∃ t : Int → Bool,
      silentSegment machine (cfg 30 b (prepared base b m xs))
        (cfg (if m % 2 = 0 then 18 else 37) h t) n := by
  by_cases h0 : m = 0
  · subst m
    obtain ⟨h0,h1⟩ := prepared_zero base b xs
    refine ⟨3, by omega, b+1, prepared base b 0 xs, ?_⟩
    simpa using zero_residual b (prepared base b 0 xs) h0 h1
  by_cases h1 : m = 1
  · subst m
    let t := after base b (UnaryBank.encode (0::xs))
    refine ⟨3, by omega, b+3, put (put (put t b true) (b+1) false) (b+2) false, ?_⟩
    simpa [prepared_one, t] using residual_one_step base b xs
  by_cases h2 : m = 2
  · subst m
    let bs := put base b true
    let s := false :: UnaryBank.encode (xs ++ [0])
    refine ⟨2 * s.length + 6, by omega, b+2, after bs (b+1) s, ?_⟩
    simpa [prepared_two, bs, s] using exceptional_cycle bs b (xs ++ [0]) (by simp [bs, put])
  have hm : 3 ≤ m := by omega
  by_cases he : m % 2 = 0
  · have h := even_to_scanner (put base b true) b m (xs ++ [0]) (by simp [put]) hm he
    dsimp only at h
    let k := NativeHalfLoopArithmetic.regularCount m - 1
    let g := boundary b k + 1
    let bs := bases (put base b true) b k
    let vs := tailValues (xs ++ [0]) k ++ [0]
    let n := totalDuration (value m) (tailValues (xs ++ [0])) k +
      duration (value m) (tailValues (xs ++ [0])) k + (2 * (false :: UnaryBank.encode vs).length + 6)
    refine ⟨n, ?_, g+2, after (put bs g true) (g+1) (false :: UnaryBank.encode vs), ?_⟩
    · dsimp [n, duration]; omega
    · simpa [prepared_large base b m xs hm, bases, boundary, suffix, value, tailValues, he, k, g, bs, vs, n] using h
  · have ho : m % 2 = 1 := by omega
    have h := maximal_odd_to_state37 (put base b true) b m (xs ++ [0]) (by simp [put]) hm ho
    dsimp only at h
    let k := NativeHalfLoopArithmetic.regularCount m - 1
    let g := boundary b k + 1
    let t := after (bases (put base b true) b k) g (UnaryBank.encode (0 :: tailValues (xs ++ [0]) k))
    let n := totalDuration (value m) (tailValues (xs ++ [0])) k +
      duration (value m) (tailValues (xs ++ [0])) k + 3
    refine ⟨n, ?_, g+3, put (put (put t g true) (g+1) false) (g+2) false, ?_⟩
    · dsimp [n, duration]; omega
    · simpa [prepared_large base b m xs hm, bases, boundary, suffix, value, tailValues, he, k, g, t, n] using h
end Shared.Beeping.NPcoNP.NativeHalfAllResiduals
