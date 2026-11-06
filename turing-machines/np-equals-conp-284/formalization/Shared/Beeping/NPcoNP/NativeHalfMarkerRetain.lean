import Shared.Beeping.NPcoNP.NativeHalfState1FiniteSupport
import Shared.Beeping.NPcoNP.NativeHalfState27Scan

/-! Conditional left-scanner progress retaining a supplied marker. -/
namespace Shared.Beeping.NPcoNP.NativeHalfMarkerRetain

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfReturn23
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState1FiniteSupport

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem scan_left_exact (k : Nat) (h : Int) (t : Int → Bool)
    (hz : ∀ p ≤ h - (k : Int), t p = false) :
    ∀ (phase : Bool), ∃ n : Nat, 0 < n ∧ n ≤ k + 2 ∧
      silentSegment machine (cfg (if phase then 24 else 23) h t)
        (cfg 1 (h - (n : Int)) t) n := by
  induction k generalizing h with
  | zero =>
    intro phase
    have h0 : t h = false := hz h (by simp)
    have h1 : t (h-1) = false := hz (h-1) (by simp)
    cases phase with
    | false =>
      refine ⟨2, by omega, by omega, ?_⟩
      have ha := oneSeg machine _ _ (step23_zero h t h0)
      have hb := oneSeg machine _ _ (step24_zero (h-1) t h1)
      have he : h - 1 - 1 = h - 2 := by omega
      simpa [he] using segAdd machine _ _ _ 1 1 ha hb
    | true =>
      refine ⟨1, by omega, by omega, ?_⟩
      simpa using oneSeg machine _ _ (step24_zero h t h0)
  | succ k ih =>
    intro phase
    have hz' : ∀ p ≤ (h-1) - (k : Int), t p = false := by
      intro p hp
      apply hz p
      simp only [Nat.cast_succ] at *
      omega
    cases phase with
    | false =>
      cases hv : t h with
      | false =>
        obtain ⟨n, hp, bound, hs⟩ := ih (h-1) hz' true
        refine ⟨1+n, by omega, by omega, ?_⟩
        have ha := oneSeg machine _ _ (step23_zero h t hv)
        have he : h-1-(n : Int) = h - ((1+n : Nat) : Int) := by omega
        simpa [he] using segAdd machine _ _ _ 1 n ha hs
      | true =>
        obtain ⟨n, hp, bound, hs⟩ := ih (h-1) hz' false
        refine ⟨1+n, by omega, by omega, ?_⟩
        have ha := oneSeg machine _ _ (step23_one h t hv)
        have he : h-1-(n : Int) = h - ((1+n : Nat) : Int) := by omega
        simpa [he] using segAdd machine _ _ _ 1 n ha hs
    | true =>
      cases hv : t h with
      | false =>
        refine ⟨1, by omega, by omega, ?_⟩
        simpa using oneSeg machine _ _ (step24_zero h t hv)
      | true =>
        obtain ⟨n, hp, bound, hs⟩ := ih (h-1) hz' false
        refine ⟨1+n, by omega, by omega, ?_⟩
        have ha := oneSeg machine _ _ (step24_one h t hv)
        have he : h-1-(n : Int) = h - ((1+n : Nat) : Int) := by omega
        simpa [he] using segAdd machine _ _ _ 1 n ha hs

theorem result_preserves_above (t : Int → Bool) (h p : Int) (j : Nat)
    (hp : h < p) : result t h j p = t p := by
  unfold result
  rw [put_other _ _ _ _ (by omega)]
  simp [cleared, show ¬(h - (j : Int) < p ∧ p ≤ h) by omega]

/-- The 23/24 return and state-1 carry preserve any marker at or to the right
of the original head, when an explicit left-zero tail guarantees progress. -/
theorem marker_to_27 (k : Nat) (h p : Int) (t : Int → Bool)
    (hz : ∀ q ≤ h - (k : Int), t q = false)
    (hph : h ≤ p) (hp : t p = true) :
    ∃ (n j : Nat), 0 < n ∧
      silentSegment machine (cfg 23 h t)
        (cfg 27 (h - (n : Int) - (j : Int) + 1) (result t (h - (n : Int)) j)) (n + (j+1)) ∧
      h - (n : Int) - (j : Int) + 1 ≤ p ∧
      result t (h - (n : Int)) j p = true := by
  obtain ⟨n, hn, _, hs⟩ := scan_left_exact k h t hz false
  let h1 : Int := h - (n : Int)
  let z : Int := min (h - (k : Int)) h1
  let d : Nat := (h1-z).toNat
  have hd : (d : Int) = h1-z := by
    apply Int.toNat_of_nonneg
    dsimp [z]
    omega
  have hzpos : t (h1-(d : Int)) = false := by
    have hzle : h1-(d : Int) ≤ h - (k : Int) := by
      rw [hd]
      dsimp [z]
      omega
    exact hz _ hzle
  obtain ⟨j, _, hj⟩ := first_zero d h1 t hzpos
  have hcarry := scan t h1 j hj
  have hjoined := segAdd machine _ _ _ n (j+1) hs hcarry
  refine ⟨n, j, hn, ?_, ?_, ?_⟩
  · simpa [h1] using hjoined
  · omega
  · rw [result_preserves_above t h1 p j (by dsimp [h1]; omega)]
    exact hp

end Shared.Beeping.NPcoNP.NativeHalfMarkerRetain


namespace Shared.Beeping.NPcoNP.NativeHalfMarkerRetain

/-- A known one at or to the right of the head has a least such offset. -/
theorem first_one (h p : Int) (t : Int → Bool) (hp : h ≤ p) (hone : t p = true) :
    ∃ j : Nat, (∀ i : Nat, i < j → t (h + (i : Int)) = false) ∧
      t (h + (j : Int)) = true := by
  let k : Nat := (p-h).toNat
  have hk : (k : Int) = p-h := Int.toNat_of_nonneg (by omega)
  have hex : ∃ j : Nat, t (h + (j : Int)) = true := by
    refine ⟨k, ?_⟩
    have he : h + (k : Int) = p := by omega
    rw [he]
    exact hone
  let j := Nat.find hex
  refine ⟨j, ?_, Nat.find_spec hex⟩
  intro i hi
  have hn : ¬ t (h + (i : Int)) = true := Nat.find_min hex hi
  cases he : t (h + (i : Int)) <;> simp_all

end Shared.Beeping.NPcoNP.NativeHalfMarkerRetain

namespace Shared.Beeping.NPcoNP.NativeHalfMarkerRetain
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState27Scan

/-- A supplied left-zero tail and a supplied rightward marker force the
literal state-23 machine to reach state 28 in finite positive silent time. -/
theorem marker_to_28 (k : Nat) (h p : Int) (t : Int → Bool)
    (hz : ∀ q ≤ h - (k : Int), t q = false)
    (hph : h ≤ p) (hp : t p = true) :
    ∃ (duration : Nat) (e : Config 284), 0 < duration ∧ e.state = 28 ∧
      silentSegment machine (cfg 23 h t) e duration := by
  obtain ⟨n, j, hn, hs, hmarkpos, hmark⟩ := marker_to_27 k h p t hz hph hp
  let h27 : Int := h - (n : Int) - (j : Int) + 1
  let t27 : Int → Bool := result t (h - (n : Int)) j
  obtain ⟨l, hzeros, hone⟩ := first_one h27 p t27 hmarkpos hmark
  have hscan := scan_to_one h27 t27 l hzeros hone
  let e : Config 284 := cfg 28 (h27 + (l : Int) + 1) (put t27 (h27 + (l : Int)) false)
  refine ⟨n+(j+1)+(l+1), e, by omega, rfl, ?_⟩
  exact segAdd machine _ _ _ (n+(j+1)) (l+1) hs hscan

end Shared.Beeping.NPcoNP.NativeHalfMarkerRetain
