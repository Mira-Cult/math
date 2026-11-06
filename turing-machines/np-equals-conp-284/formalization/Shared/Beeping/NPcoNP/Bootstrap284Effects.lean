import Shared.Beeping.NPcoNP.Bootstrap284Scans

/-! Pointwise descriptions of the finite bootstrap scan effects. These
lemmas expose the cells rewritten by each segment for use in a compact trace
certificate; they do not certify the blank-start bootstrap trace. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284Effects

open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.Bootstrap284Scans

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Each visited first cell is cleared and the next cell is set. -/
theorem leftEffect_pair (n i : Nat) (h : Int) (t : Int → Bool) (hi : i<n) :
    leftEffect n t h (h-2*(i : Int))=false ∧
    leftEffect n t h (h-2*(i : Int)-1)=true := by
  induction n generalizing h t i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      have h0 := leftEffect_outside n (h-2) h (put (put t h false) (h-1) true) (by left; omega)
      have h1 := leftEffect_outside n (h-2) (h-1) (put (put t h false) (h-1) true) (by left; omega)
      simp only [leftEffect, Nat.cast_zero, mul_zero, sub_zero]
      rw [h0,h1]
      simp [put, show h ≠ h-1 by omega]
    | succ i =>
      have hi' : i<n := by omega
      have hh := ih i (h-2) (put (put t h false) (h-1) true) hi'
      have he : (h-2)-2*(i : Int)=h-2*((i+1 : Nat) : Int) := by push_cast; omega
      rw [he] at hh
      simpa only [leftEffect,Nat.succ_eq_add_one] using hh

/-- Filling changes each visited second cell to one, preserving its paired
first cell. The result is independent of the initial value of the second. -/
theorem fillEffect_pair (n i : Nat) (h : Int) (t : Int → Bool) (hi : i<n) :
    fillEffect n t h (h-2*(i : Int))=t (h-2*(i : Int)) ∧
    fillEffect n t h (h-2*(i : Int)-1)=true := by
  induction n generalizing h t i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      have h0 := fillEffect_outside n (h-2) h (put t (h-1) true) (by left; omega)
      have h1 := fillEffect_outside n (h-2) (h-1) (put t (h-1) true) (by left; omega)
      simp only [fillEffect,Nat.cast_zero,mul_zero,sub_zero]
      rw [h0,h1]
      simp [put, show h ≠ h-1 by omega]
    | succ i =>
      have hi' : i<n := by omega
      have hh := ih i (h-2) (put t (h-1) true) hi'
      have he : (h-2)-2*(i : Int)=h-2*((i+1 : Nat) : Int) := by push_cast; omega
      rw [he] at hh
      have hneq : h-2*((i+1 : Nat) : Int) ≠ h-1 := by push_cast; omega
      rw [put_other _ _ _ _ hneq] at hh
      simpa only [fillEffect,Nat.succ_eq_add_one] using hh

end Shared.Beeping.NPcoNP.Bootstrap284Effects
