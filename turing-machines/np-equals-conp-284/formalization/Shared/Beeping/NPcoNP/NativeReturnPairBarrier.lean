import Shared.Beeping.NPcoNP.NativeHalfReturn23
import Shared.Beeping.NPcoNP.NativeHalfOddReturn

/-! A leftward two-phase scanner can return only after reading a zero pair.
This exposes the stopping pair, allowing selector prefixes to act as barriers. -/
namespace Shared.Beeping.NPcoNP.NativeReturnPairBarrier
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfReturn23
open Shared.Beeping.NPcoNP.NativeHalfOddReturn
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- Two-phase left scanner over an unchanged tape: its exit witnesses the
actual adjacent zero pair. Phase one requires the previously read zero. -/
theorem scan_pair {states : Nat} (M : Machine states) (a b exit : Fin states)
    (a0 : ∀ h t, t h=false → M.step (cfg a h t)=(cfg b (h-1) t,false))
    (a1 : ∀ h t, t h=true → M.step (cfg a h t)=(cfg a (h-1) t,false))
    (b0 : ∀ h t, t h=false → M.step (cfg b h t)=(cfg exit (h-1) t,false))
    (b1 : ∀ h t, t h=true → M.step (cfg b h t)=(cfg a (h-1) t,false))
    (k : Nat) (h : Int) (t : Int → Bool)
    (tail : ∀ q, q≤h-(k : Int) → t q=false) :
    ∀ (phase : Bool), (phase=true → t (h+1)=false) →
    ∃ n : Nat, (if phase then 1 else 2)≤n ∧ n≤k+2 ∧
      t (h-(n : Int)+1)=false ∧ t (h-(n : Int)+2)=false ∧
      silentSegment M (cfg (if phase then b else a) h t) (cfg exit (h-(n : Int)) t) n := by
  induction k generalizing h with
  | zero =>
    intro phase prior
    have h0 : t h=false := tail h (by simp)
    have h1 : t (h-1)=false := tail (h-1) (by simp)
    cases phase with
    | false =>
      refine ⟨2,by decide,by decide,?_,?_,?_⟩
      · have he : h-2+1=h-1 := by omega
        simpa only [Nat.cast_ofNat, he] using h1
      · simpa using h0
      · have hs := segAdd M _ _ _ 1 1 (oneSeg M _ _ (a0 h t h0)) (oneSeg M _ _ (b0 (h-1) t h1))
        simpa [show h-1-1=h-2 by omega] using hs
    | true =>
      refine ⟨1,by decide,by decide,?_,?_,?_⟩
      · simpa using h0
      · have he : h-1+2=h+1 := by omega
        simpa only [Nat.cast_one, he] using prior rfl
      · simpa using oneSeg M _ _ (b0 h t h0)
  | succ k ih =>
    intro phase prior
    have tail' : ∀ q, q≤(h-1)-(k : Int) → t q=false := by
      intro q hq
      apply tail q
      simp only [Nat.cast_succ] at *
      omega
    cases phase with
    | false =>
      cases hv : t h with
      | false =>
        have hp : true=true → t ((h-1)+1)=false := by intro _; simpa using hv
        obtain ⟨n,hn,hb,hz1,hz2,hs⟩ := ih (h-1) tail' true hp
        refine ⟨1+n,by simp at hn ⊢ <;> omega,by omega,?_,?_,?_⟩
        · have he : (h-1)-(n : Int)+1=h-((1+n : Nat):Int)+1 := by push_cast; omega
          simpa only [he] using hz1
        · have he : (h-1)-(n : Int)+2=h-((1+n : Nat):Int)+2 := by push_cast; omega
          simpa only [he] using hz2
        · have hall := segAdd M _ _ _ 1 n (oneSeg M _ _ (a0 h t hv)) hs
          have he : (h-1)-(n : Int)=h-((1+n : Nat):Int) := by push_cast; omega
          simpa [he] using hall
      | true =>
        obtain ⟨n,hn,hb,hz1,hz2,hs⟩ := ih (h-1) tail' false (by intro h; contradiction)
        refine ⟨1+n,by simp at hn ⊢ <;> omega,by omega,?_,?_,?_⟩
        · have he : (h-1)-(n : Int)+1=h-((1+n : Nat):Int)+1 := by push_cast; omega
          simpa only [he] using hz1
        · have he : (h-1)-(n : Int)+2=h-((1+n : Nat):Int)+2 := by push_cast; omega
          simpa only [he] using hz2
        · have hall := segAdd M _ _ _ 1 n (oneSeg M _ _ (a1 h t hv)) hs
          have he : (h-1)-(n : Int)=h-((1+n : Nat):Int) := by push_cast; omega
          simpa [he] using hall
    | true =>
      cases hv : t h with
      | false =>
        refine ⟨1,by decide,by omega,?_,?_,?_⟩
        · simpa using hv
        · have he : h-1+2=h+1 := by omega
          simpa only [Nat.cast_one, he] using prior rfl
        · simpa using oneSeg M _ _ (b0 h t hv)
      | true =>
        obtain ⟨n,hn,hb,hz1,hz2,hs⟩ := ih (h-1) tail' false (by intro h; contradiction)
        refine ⟨1+n,by simp at hn ⊢ <;> omega,by omega,?_,?_,?_⟩
        · have he : (h-1)-(n : Int)+1=h-((1+n : Nat):Int)+1 := by push_cast; omega
          simpa only [he] using hz1
        · have he : (h-1)-(n : Int)+2=h-((1+n : Nat):Int)+2 := by push_cast; omega
          simpa only [he] using hz2
        · have hall := segAdd M _ _ _ 1 n (oneSeg M _ _ (b1 h t hv)) hs
          have he : (h-1)-(n : Int)=h-((1+n : Nat):Int) := by push_cast; omega
          simpa [he] using hall

/-- If no zero pair starts strictly above the barrier, the state-23 scan
finishes strictly to its left. -/
theorem scan23_below (h d z : Int) (t : Int → Bool)
    (left : ∀ q, q≤z → t q=false)
    (safe : ∀ q, d+2≤q → q≤h → t q=false → t (q-1)=true) :
    ∃ n : Nat, 2≤n ∧ h-(n : Int)<d ∧
      silentSegment machine (cfg 23 h t) (cfg 1 (h-(n : Int)) t) n := by
  let k := (h-min z h).toNat
  have hk : h-(k : Int)≤z := by
    have hn : 0≤h-min z h := by omega
    have he : (k : Int)=h-min z h := Int.toNat_of_nonneg hn
    omega
  have ht : ∀ q, q≤h-(k : Int) → t q=false := by intro q hq; exact left q (le_trans hq hk)
  obtain ⟨n,hn,_hb,hz1,hz2,hseg⟩ := scan_pair machine 23 24 1
    step23_zero step23_one step24_zero step24_one k h t ht false (by intro hf; contradiction)
  simp only [Bool.false_eq_true, if_false] at hn
  have hbelow : h-(n : Int)<d := by
    by_contra hc
    have hq : d+2≤h-(n : Int)+2 := by omega
    have hqh : h-(n : Int)+2≤h := by omega
    have ho := safe (h-(n : Int)+2) hq hqh hz2
    have he : h-(n : Int)+2-1=h-(n : Int)+1 := by omega
    rw [he,hz1] at ho
    contradiction
  exact ⟨n,hn,hbelow,hseg⟩

/-- The state-25/26 return obeys the identical barrier, with state 95
as its exit. -/
theorem scan25_below (h d z : Int) (t : Int → Bool)
    (left : ∀ q, q≤z → t q=false)
    (safe : ∀ q, d+2≤q → q≤h → t q=false → t (q-1)=true) :
    ∃ n : Nat, 2≤n ∧ h-(n : Int)<d ∧
      silentSegment machine (cfg 25 h t) (cfg 95 (h-(n : Int)) t) n := by
  let k := (h-min z h).toNat
  have hk : h-(k : Int)≤z := by
    have hn : 0≤h-min z h := by omega
    have he : (k : Int)=h-min z h := Int.toNat_of_nonneg hn
    omega
  have ht : ∀ q, q≤h-(k : Int) → t q=false := by intro q hq; exact left q (le_trans hq hk)
  obtain ⟨n,hn,_hb,hz1,hz2,hseg⟩ := scan_pair machine 25 26 95
    step25_zero step25_one step26_zero step26_one k h t ht false (by intro hf; contradiction)
  simp only [Bool.false_eq_true, if_false] at hn
  have hbelow : h-(n : Int)<d := by
    by_contra hc
    have hq : d+2≤h-(n : Int)+2 := by omega
    have hqh : h-(n : Int)+2≤h := by omega
    have ho := safe (h-(n : Int)+2) hq hqh hz2
    have he : h-(n : Int)+2-1=h-(n : Int)+1 := by omega
    rw [he,hz1] at ho
    contradiction
  exact ⟨n,hn,hbelow,hseg⟩

#print axioms scan23_below
#print axioms scan25_below
end Shared.Beeping.NPcoNP.NativeReturnPairBarrier
