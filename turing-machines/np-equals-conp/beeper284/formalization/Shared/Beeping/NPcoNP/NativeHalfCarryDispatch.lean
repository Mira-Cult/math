import Shared.Beeping.NPcoNP.NativeHalfState1Scan
import Shared.Beeping.NPcoNP.NativeHalfState27Scan

/-! Exact literal-table continuation from the prepared state-1 boundary.
The finite carry and the two following zero cells are explicit hypotheses.
This does not assert blank-start reachability or a complete HALF operation. -/
namespace Shared.Beeping.NPcoNP.NativeHalfCarryDispatch

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState27Scan

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The erased carry followed by two zero cells is exactly the interval
traversed by state 27. -/
theorem carry_zeroes (t : Int → Bool) (h : Int) (k : Nat)
    (h₁ : t (h+1) = false) (h₂ : t (h+2) = false)
    (i : Nat) (hi : i < k+2) :
    result t h k (h-(k : Int)+1+(i : Int)) = false := by
  let p := h-(k : Int)+1+(i : Int)
  change result t h k p = false
  have hne : p ≠ h-(k : Int) := by dsimp [p]; omega
  by_cases hk : i < k
  · have hp : h-(k : Int) < p ∧ p ≤ h := by dsimp [p]; omega
    simp [result, put, cleared, hne, hp]
  · have hi' : i = k ∨ i = k+1 := by omega
    have hout : ¬ (h-(k : Int) < p ∧ p ≤ h) := by dsimp [p]; omega
    have hv : t p = false := by
      rcases hi' with rfl | rfl
      · have hp : p = h+1 := by dsimp [p]; omega
        simpa [hp] using h₁
      · have hp : p = h+2 := by dsimp [p]; omega
        simpa [hp] using h₂
    simp [result, put, cleared, hne, hout, hv]

theorem carry_next_one (t : Int → Bool) (h : Int) (k : Nat)
    (h₃ : t (h+3) = true) :
    result t h k ((h-(k : Int)+1)+(k+2)) = true := by
  have he : (h-(k : Int)+1)+((k : Int)+2) = h+3 := by omega
  rw [he]
  have hne : h+3 ≠ h-(k : Int) := by omega
  have hout : ¬ (h-(k : Int) < h+3 ∧ h+3 ≤ h) := by omega
  simp [result, put, cleared, hne, hout, h₃]

/-- On the stated local pattern the carry and rightward scan produce exactly
one state-28 boundary in `2*k+4` silent transitions. The whole output tape
is the explicit composition of the two writes. -/
theorem dispatch (t : Int → Bool) (h : Int) (k : Nat)
    (hm : downHolds t h (List.replicate k true ++ [false]))
    (h₁ : t (h+1) = false) (h₂ : t (h+2) = false)
    (h₃ : t (h+3) = true) :
    silentSegment machine (cfg 1 h t)
      (cfg 28 (h+4) (put (result t h k) (h+3) false)) (2*k+4) := by
  have ha := scan t h k hm
  have hz : ∀ i : Nat, i < k+2 →
      result t h k ((h-(k : Int)+1)+(i : Int)) = false := by
    intro i hi
    exact carry_zeroes t h k h₁ h₂ i hi
  have ho := carry_next_one t h k h₃
  have hb := scan_to_one (h-(k : Int)+1) (result t h k) (k+2) hz ho
  have hc := segAdd machine _ _ _ (k+1) (k+2+1) ha hb
  have hpos : (h-(k : Int)+1) + ((k : Int)+2) + 1 = h+4 := by omega
  have hwrite : (h-(k : Int)+1) + ((k : Int)+2) = h+3 := by omega
  have htime : (k+1)+(k+2+1) = 2*k+4 := by omega
  simp only [Nat.cast_add, Nat.cast_ofNat] at hc
  rw [hpos, hwrite, htime] at hc
  exact hc

end Shared.Beeping.NPcoNP.NativeHalfCarryDispatch
