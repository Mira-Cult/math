import Shared.Beeping.NPcoNP.NativeHalfOddFinish

/-! The state-95 return stops immediately after reading a zero. -/
namespace Shared.Beeping.NPcoNP.NativeHalfState95Stop

open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfOddFinish
open Shared.Beeping.NPcoNP.NativeHalfState28Exact

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- The supplied zero forces finite progress, and the final head sits
immediately left of the zero read by state 95. -/
theorem scan95_exact_with_stop (k : Nat) (h : Int) (t : Int → Bool)
    (hz : t (h-(k : Int))=false) :
    ∃ n : Nat, 0<n ∧ n≤k+1 ∧ t (h-(n : Int)+1)=false ∧
      (∀ p, h-(n : Int)+1<p → p≤h → t p=true) ∧
      silentSegment machine (cfg 95 h t)
        (cfg 1 (h-(n : Int)) (clearRange t (h-(n : Int)+2) (h+1))) n := by
  induction k generalizing h t with
  | zero =>
    have h0 : t h=false := by simpa using hz
    refine ⟨1,by omega,by omega,by simpa using h0,by intro p hp hp'; omega,?_⟩
    have hs := oneSeg machine _ _ (step95_zero h t h0)
    change silentSegment machine (cfg 95 h t)
      (cfg 1 (h-1) (clearRange t (h-1+2) (h+1))) 1
    rw [show h-1+2=h+1 by omega,clear_empty]
    exact hs
  | succ k ih =>
    cases hv : t h with
    | false =>
      refine ⟨1,by omega,by omega,by simpa using hv,by intro p hp hp'; omega,?_⟩
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
      obtain ⟨n,hn,hbound,hstop,hones,hs⟩ := ih (h-1) t' hz'
      have hlo : (h-1)-(n : Int)+2≤h := by omega
      have hclear : clearRange t' ((h-1)-(n : Int)+2) ((h-1)+1) =
          clearRange t (h-((1+n : Nat) : Int)+2) (h+1) := by
        have hl : (h-1)-(n : Int)+2=h-((1+n : Nat) : Int)+2 := by push_cast; omega
        rw [show (h-1)+1=h by omega,clear_right_edge t _ h hlo,hl]
      rw [hclear] at hs
      have hall := segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step95_one h t hv)) hs
      have hp : (h-1)-(n : Int)=h-((1+n : Nat) : Int) := by push_cast; omega
      refine ⟨1+n,by omega,by omega,?_,?_,?_⟩
      · have hne' : (h-1)-(n : Int)+1≠h := by omega
        change put t h false ((h-1)-(n : Int)+1)=false at hstop
        rw [put_other _ _ _ _ hne'] at hstop
        simpa only [← hp] using hstop
      · intro p hp' hp''
        by_cases he : p=h
        · subst p
          exact hv
        · have hone := hones p (by rw [hp]; exact hp') (by omega)
          change put t h false p=true at hone
          rw [put_other _ _ _ _ he] at hone
          exact hone
      · simpa [hp] using hall

end Shared.Beeping.NPcoNP.NativeHalfState95Stop

#print axioms Shared.Beeping.NPcoNP.NativeHalfState95Stop.scan95_exact_with_stop
