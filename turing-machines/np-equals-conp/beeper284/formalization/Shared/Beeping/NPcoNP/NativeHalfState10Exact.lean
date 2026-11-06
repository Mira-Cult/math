import Shared.Beeping.NPcoNP.NativeHalfState10Progress

/-! Exact physical effect of the selected state-10 zero-filling scan. The
input supplies a finite zero run followed by one; the output specifies the
whole infinite tape and the exact positive silent transition count. -/
namespace Shared.Beeping.NPcoNP.NativeHalfState10Exact

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Progress

def fillRange (t : Int → Bool) (lo hi : Int) (p : Int) : Bool :=
  if lo≤p ∧ p<hi then true else t p

theorem fill_empty (t : Int → Bool) (h : Int) : fillRange t h h=t := by
  funext p
  have hn : ¬ (h≤p ∧ p<h) := by omega
  simp [fillRange,hn]

theorem fill_tail (t : Int → Bool) (h hi : Int) (hhi : h+1≤hi) :
    fillRange (setAt h t) (h+1) hi = fillRange t h hi := by
  funext p
  by_cases hp : p=h
  · subst p
    have hn : ¬ (h+1≤h ∧ h<hi) := by omega
    have hy : h≤h ∧ h<hi := by omega
    simp [fillRange,setAt,hn,hy]
  · by_cases hr : h≤p ∧ p<hi
    · have hr' : h+1≤p ∧ p<hi := by omega
      simp [fillRange,hr,hr']
    · have hr' : ¬ (h+1≤p ∧ p<hi) := by omega
      simp [fillRange,setAt,hp,hr,hr']

/-- Fill exactly the supplied zero run, stop on the following one, and
move left to state 97. Every other tape cell is preserved. -/
theorem scan10_exact (k : Nat) (h : Int) (t : Int → Bool)
    (hz : ∀ i : Nat, i<k → t (h+(i : Int))=false)
    (hm : t (h+(k : Int))=true) :
    silentSegment machine (cfg 10 h t)
      (cfg 97 (h+(k : Int)-1) (fillRange t h (h+(k : Int)))) (k+1) := by
  induction k generalizing h t with
  | zero =>
    have ht : t h=true := by simpa using hm
    have hs := oneSeg machine _ _ (step10_one h t ht)
    simpa [fill_empty] using hs
  | succ k ih =>
    have h0 : t h=false := by simpa using hz 0 (by omega)
    let t' := setAt h t
    have hz' : ∀ i : Nat, i<k → t' ((h+1)+(i : Int))=false := by
      intro i hi
      have hn : (h+1)+(i : Int) ≠ h := by omega
      have he : (h+1)+(i : Int)=h+((i+1 : Nat) : Int) := by push_cast; omega
      change (if (h+1)+(i : Int)=h then true else t ((h+1)+(i : Int)))=false
      rw [if_neg hn,he]
      exact hz (i+1) (by omega)
    have hn : (h+1)+(k : Int) ≠ h := by omega
    have he : (h+1)+(k : Int)=h+((Nat.succ k : Nat) : Int) := by push_cast; omega
    have hm' : t' ((h+1)+(k : Int))=true := by
      change (if (h+1)+(k : Int)=h then true else t ((h+1)+(k : Int)))=true
      rw [if_neg hn,he]
      exact hm
    have htape : fillRange t' (h+1) ((h+1)+(k : Int)) =
        fillRange t h (h+((Nat.succ k : Nat) : Int)) := by
      rw [← he]
      exact fill_tail t h ((h+1)+(k : Int)) (by omega)
    have hstep := oneSeg machine _ _ (step10_zero h t h0)
    have hrest := ih (h+1) t' hz' hm'
    rw [htape] at hrest
    have hall := segAdd machine _ _ _ 1 (k+1) hstep hrest
    simpa [Int.add_assoc, Int.add_comm, Int.add_left_comm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

end Shared.Beeping.NPcoNP.NativeHalfState10Exact

#print axioms Shared.Beeping.NPcoNP.NativeHalfState10Exact.scan10_exact
