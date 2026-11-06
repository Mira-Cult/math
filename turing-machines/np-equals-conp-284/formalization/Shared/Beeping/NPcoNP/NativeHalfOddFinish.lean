import Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress
import Shared.Beeping.NPcoNP.NativeHalfState28Exact

/-! Exact state-95 leftward cleanup and its composition with the odd native
HALF return. Input layout and blank-start reachability remain separate. -/
namespace Shared.Beeping.NPcoNP.NativeHalfOddFinish

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfAllResiduals
open Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

theorem row95_zero : machine.table.row 95 false = ⟨false,.left,1,false⟩ := by decide
theorem row95_one : machine.table.row 95 true = ⟨false,.left,95,false⟩ := by decide

theorem step95_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 95 h t)=(cfg 1 (h-1) t,false) := by
  have hw : (⟨95,h,t⟩ : Config 284).write false=t := by rw [← ht]; exact write_current _
  simp [cfg,Machine.step,ht,row95_zero,Move.apply,hw]

theorem step95_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 95 h t)=(cfg 95 (h-1) (put t h false),false) := by
  have hw : (⟨95,h,t⟩ : Config 284).write false=put t h false := rfl
  simp [cfg,Machine.step,ht,row95_one,Move.apply,hw]

theorem clear_right_edge (t : Int → Bool) (lo h : Int) (hlo : lo≤h) :
    clearRange (put t h false) lo h=clearRange t lo (h+1) := by
  funext p
  by_cases hp : p=h
  · subst p
    have hleft : ¬ (lo≤h ∧ h<h) := by omega
    have hright : lo≤h ∧ h<h+1 := by omega
    simp [clearRange,put,hleft,hright]
  · by_cases hr : lo≤p ∧ p<h+1
    · have hr' : lo≤p ∧ p<h := by omega
      simp [clearRange,hr,hr']
    · have hr' : ¬ (lo≤p ∧ p<h) := by omega
      simp [clearRange,put,hp,hr,hr'] <;> omega

/-- State 95 reaches state 1 within `k+1` steps when a zero occurs at
distance `k` to the left. The exact interval cleared is recorded. -/
theorem scan95_exact (k : Nat) (h : Int) (t : Int → Bool)
    (hz : t (h-(k : Int))=false) :
    ∃ n : Nat, 0<n ∧ n≤k+1 ∧
      silentSegment machine (cfg 95 h t)
        (cfg 1 (h-(n : Int)) (clearRange t (h-(n : Int)+2) (h+1))) n := by
  induction k generalizing h t with
  | zero =>
    have h0 : t h=false := by simpa using hz
    refine ⟨1,by omega,by omega,?_⟩
    have hs := oneSeg machine _ _ (step95_zero h t h0)
    change silentSegment machine (cfg 95 h t)
      (cfg 1 (h-1) (clearRange t (h-1+2) (h+1))) 1
    rw [show h-1+2=h+1 by omega,clear_empty]
    exact hs
  | succ k ih =>
    cases hv : t h with
    | false =>
      refine ⟨1,by omega,by omega,?_⟩
      have hs := oneSeg machine _ _ (step95_zero h t hv)
      change silentSegment machine (cfg 95 h t)
        (cfg 1 (h-1) (clearRange t (h-1+2) (h+1))) 1
      rw [show h-1+2=h+1 by omega,clear_empty]
      exact hs
    | true =>
      let t' := put t h false
      have hpos : (h-1)-(k : Int)=h-((Nat.succ k : Nat) : Int) := by push_cast; omega
      have hne : (h-1)-(k : Int)≠h := by omega
      have hz' : t' ((h-1)-(k : Int))=false := by
        rw [show t' ((h-1)-(k : Int))=t ((h-1)-(k : Int)) from put_other _ _ _ _ hne,hpos]
        exact hz
      obtain ⟨n,hn,hbound,hs⟩ := ih (h-1) t' hz'
      have hlo : (h-1)-(n : Int)+2≤h := by omega
      have hclear : clearRange t' ((h-1)-(n : Int)+2) ((h-1)+1) =
          clearRange t (h-((1+n : Nat) : Int)+2) (h+1) := by
        have hl : (h-1)-(n : Int)+2=h-((1+n : Nat) : Int)+2 := by push_cast; omega
        rw [show (h-1)+1=h by omega,clear_right_edge t _ h hlo,hl]
      rw [hclear] at hs
      have hall := segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step95_one h t hv)) hs
      have hp : (h-1)-(n : Int)=h-((1+n : Nat) : Int) := by push_cast; omega
      refine ⟨1+n,by omega,by omega,?_⟩
      simpa [hp] using hall

/-- Every actual blank-start visit to state 95 silently reaches state 1,
with an explicitly described finite cleared interval. -/
theorem reachable_95_to1 (time : Nat) (hs : (machine.system.run time).state=95) :
    ∃ n : Nat, 0<n ∧
      silentSegment machine (machine.system.run time)
        (cfg 1 ((machine.system.run time).head-(n : Int))
          (clearRange (machine.system.run time).tape
            ((machine.system.run time).head-(n : Int)+2) ((machine.system.run time).head+1))) n := by
  obtain ⟨z,hz⟩ := NativeHalfReturnFiniteSupport.run_has_left_zero time
  let c := machine.system.run time
  let k := (c.head-min z c.head).toNat
  have hk : c.head-(k : Int)≤z := by
    have hn : 0≤c.head-min z c.head := by omega
    have he : (k : Int)=c.head-min z c.head := Int.toNat_of_nonneg hn
    omega
  obtain ⟨n,hn,_,hseg⟩ := scan95_exact k c.head c.tape (hz _ hk)
  have hc : c=cfg 95 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    have hs' : c.state=95 := hs
    simpa only [hs'] using he
  refine ⟨n,hn,?_⟩
  simpa [← hc] using hseg

/-- Every odd prepared right-block size completes the loop, both cleanup
scans, and the state-95 return to state 1 under a left-zero-tail premise.
The returned tape is the exact finite clear applied to the state-95 tape;
the latter preserves the original prefix strictly left of the boundary. -/
theorem prepared_odd_to1 (base : Int → Bool) (b z : Int) (m : Nat) (xs : List Nat)
    (hodd : m%2=1) (hz : ∀ p ≤ z, base p=false) :
    ∃ (n₁ n₂ : Nat) (h : Int) (t : Int → Bool), 0<n₁ ∧ 0<n₂ ∧
      (∀ p<b, t p=base p) ∧
      silentSegment machine (cfg 30 b (prepared base b m xs))
        (cfg 1 (h-(n₂ : Int)) (clearRange t (h-(n₂ : Int)+2) (h+1))) (n₁+n₂) := by
  obtain ⟨n₁,h,t,hn₁,hprefix,hfirst⟩ := prepared_odd_to95 base b z m xs hodd hz
  let a := min z (b-1)
  let k := (h-min a h).toNat
  have hk : h-(k : Int)≤a := by
    have hn : 0≤h-min a h := by omega
    have he : (k : Int)=h-min a h := Int.toNat_of_nonneg hn
    omega
  have ht : t (h-(k : Int))=false := by
    have hza : a≤z := min_le_left _ _
    have hba : a≤b-1 := min_le_right _ _
    rw [hprefix _ (by omega)]
    exact hz _ (by omega)
  obtain ⟨n₂,hn₂,_,hsecond⟩ := scan95_exact k h t ht
  exact ⟨n₁,n₂,h,t,hn₁,hn₂,hprefix,
    segAdd machine _ _ _ n₁ n₂ hfirst hsecond⟩

end Shared.Beeping.NPcoNP.NativeHalfOddFinish

#print axioms Shared.Beeping.NPcoNP.NativeHalfOddFinish.scan95_exact
#print axioms Shared.Beeping.NPcoNP.NativeHalfOddFinish.reachable_95_to1
#print axioms Shared.Beeping.NPcoNP.NativeHalfOddFinish.prepared_odd_to1
