import Shared.Beeping.NPcoNP.NativeHalfState28Progress

/-! Exact physical effect of the selected state-28 one-clearing scan. A
supplied finite one run followed by zero gives the complete output tape,
exact positive duration and empty event word. -/
namespace Shared.Beeping.NPcoNP.NativeHalfState28Exact

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Progress

def clearRange (t : Int → Bool) (lo hi : Int) (p : Int) : Bool :=
  if lo≤p ∧ p<hi then false else t p

theorem clear_empty (t : Int → Bool) (h : Int) : clearRange t h h=t := by
  funext p
  have hn : ¬ (h≤p ∧ p<h) := by omega
  simp [clearRange,hn]

theorem clear_tail (t : Int → Bool) (h hi : Int) (hhi : h+1≤hi) :
    clearRange (put t h false) (h+1) hi = clearRange t h hi := by
  funext p
  by_cases hp : p=h
  · subst p
    have hn : ¬ (h+1≤h ∧ h<hi) := by omega
    have hy : h≤h ∧ h<hi := by omega
    simp [clearRange,put,hn,hy]
  · by_cases hr : h≤p ∧ p<hi
    · have hr' : h+1≤p ∧ p<hi := by omega
      simp [clearRange,hr,hr']
    · have hr' : ¬ (h+1≤p ∧ p<hi) := by omega
      simp [clearRange,put,hp,hr,hr']

/-- Clear exactly the supplied one run, stop at the following zero and
move left to state 6, preserving every tape cell outside that run. -/
theorem scan28_exact (k : Nat) (h : Int) (t : Int → Bool)
    (ho : ∀ i : Nat, i<k → t (h+(i : Int))=true)
    (hz : t (h+(k : Int))=false) :
    silentSegment machine (cfg 28 h t)
      (cfg 6 (h+(k : Int)-1) (clearRange t h (h+(k : Int)))) (k+1) := by
  induction k generalizing h t with
  | zero =>
    have ht : t h=false := by simpa using hz
    have hs := oneSeg machine _ _ (step28_zero h t ht)
    simpa [clear_empty] using hs
  | succ k ih =>
    have h0 : t h=true := by simpa using ho 0 (by omega)
    let t' := put t h false
    have ho' : ∀ i : Nat, i<k → t' ((h+1)+(i : Int))=true := by
      intro i hi
      have hn : (h+1)+(i : Int) ≠ h := by omega
      have he : (h+1)+(i : Int)=h+((i+1 : Nat) : Int) := by push_cast; omega
      change (if (h+1)+(i : Int)=h then false else t ((h+1)+(i : Int)))=true
      rw [if_neg hn,he]
      exact ho (i+1) (by omega)
    have hn : (h+1)+(k : Int) ≠ h := by omega
    have he : (h+1)+(k : Int)=h+((Nat.succ k : Nat) : Int) := by push_cast; omega
    have hz' : t' ((h+1)+(k : Int))=false := by
      change (if (h+1)+(k : Int)=h then false else t ((h+1)+(k : Int)))=false
      rw [if_neg hn,he]
      exact hz
    have htape : clearRange t' (h+1) ((h+1)+(k : Int)) =
        clearRange t h (h+((Nat.succ k : Nat) : Int)) := by
      rw [← he]
      exact clear_tail t h ((h+1)+(k : Int)) (by omega)
    have hstep := oneSeg machine _ _ (step28_one h t h0)
    have hrest := ih (h+1) t' ho' hz'
    rw [htape] at hrest
    have hall := segAdd machine _ _ _ 1 (k+1) hstep hrest
    simpa [Int.add_assoc, Int.add_comm, Int.add_left_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

end Shared.Beeping.NPcoNP.NativeHalfState28Exact

#print axioms Shared.Beeping.NPcoNP.NativeHalfState28Exact.scan28_exact
