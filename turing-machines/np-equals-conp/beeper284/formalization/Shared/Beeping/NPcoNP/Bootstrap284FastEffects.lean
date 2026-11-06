import Shared.Beeping.NPcoNP.Bootstrap284Effects

/-! Closed pointwise implementations of bootstrap tape updates. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284FastEffects
open Shared.Beeping.NPcoNP.Bootstrap284Scans
open Shared.Beeping.NPcoNP.Bootstrap284Effects

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

def fastLeft (n : Nat) (t : Int → Bool) (h p : Int) : Bool :=
  if h-2*(n : Int)<p ∧ p≤h then decide ((h-p)%2=1) else t p

def fastFill (n : Nat) (t : Int → Bool) (h p : Int) : Bool :=
  if h-2*(n : Int)<p ∧ p≤h ∧ (h-p)%2=1 then true else t p

theorem left_eq_fast (n : Nat) (t : Int → Bool) (h : Int) : leftEffect n t h=fastLeft n t h := by
  funext p
  by_cases hp : h-2*(n : Int)<p ∧ p≤h
  · let d : Nat := (h-p).toNat
    have hd : (d : Int)=h-p := Int.toNat_of_nonneg (by omega)
    let i := d/2
    have hi : i<n := by dsimp [i]; omega
    have hpar : d%2=0 ∨ d%2=1 := by omega
    rcases hpar with heven | hodd
    · have hpos : p=h-2*(i : Int) := by dsimp [i]; omega
      have hmod : (h-p)%2=0 := by omega
      have he := (leftEffect_pair n i h t hi).1
      unfold fastLeft
      rw [if_pos hp,hmod]
      simp only [show (0 : Int) ≠ 1 by decide,decide_false]
      rw [hpos]
      exact he
    · have hpos : p=h-2*(i : Int)-1 := by dsimp [i]; omega
      have hmod : (h-p)%2=1 := by omega
      have he := (leftEffect_pair n i h t hi).2
      unfold fastLeft
      rw [if_pos hp,hmod]
      simp only [decide_true]
      rw [hpos]
      exact he
  · have ho : h<p ∨ p≤h-2*(n : Int) := by omega
    rw [leftEffect_outside n h p t ho]
    simp [fastLeft,hp]

theorem fill_eq_fast (n : Nat) (t : Int → Bool) (h : Int) : fillEffect n t h=fastFill n t h := by
  funext p
  by_cases hp : h-2*(n : Int)<p ∧ p≤h
  · let d : Nat := (h-p).toNat
    have hd : (d : Int)=h-p := Int.toNat_of_nonneg (by omega)
    let i := d/2
    have hi : i<n := by dsimp [i]; omega
    have hpar : d%2=0 ∨ d%2=1 := by omega
    rcases hpar with heven | hodd
    · have hpos : p=h-2*(i : Int) := by dsimp [i]; omega
      have hmod : (h-p)%2=0 := by omega
      have he := (fillEffect_pair n i h t hi).1
      have hg : ¬ (h-2*(n : Int)<p ∧ p≤h ∧ (h-p)%2=1) := by omega
      unfold fastFill
      rw [if_neg hg,hpos]
      exact he
    · have hpos : p=h-2*(i : Int)-1 := by dsimp [i]; omega
      have hmod : (h-p)%2=1 := by omega
      have he := (fillEffect_pair n i h t hi).2
      have hg : h-2*(n : Int)<p ∧ p≤h ∧ (h-p)%2=1 := by omega
      unfold fastFill
      rw [if_pos hg,hpos]
      exact he
  · have ho : h<p ∨ p≤h-2*(n : Int) := by omega
    have hg : ¬ (h-2*(n : Int)<p ∧ p≤h ∧ (h-p)%2=1) := by omega
    rw [fillEffect_outside n h p t ho]
    simp only [fastFill,if_neg hg]
end Shared.Beeping.NPcoNP.Bootstrap284FastEffects
