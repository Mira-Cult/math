import Shared.Beeping.NPcoNP.NativeUnit261Return1
import Shared.Beeping.NPcoNP.NativeHalfState28Exit
import Shared.Beeping.NPcoNP.NativeHalfMarkerExact
import Shared.Beeping.NPcoNP.NativeHalfState27Scan

/-! A parameterized finite return from the unit-dispatch control boundary
to state 83, with an exact output tape and explicit layout hypotheses. -/
namespace Shared.Beeping.NPcoNP.NativeUnitCarryExact83
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState27Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfMarkerExact
open Shared.Beeping.NPcoNP.NativeHalfState28Exit
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- The unit carry return has an exact positive duration. The first
one is consumed by state 27; state 28 clears the rest of the run; state 97
returns to the marker created by state 1. -/
theorem carry_to83_exact (r : Nat) (h : Int) (t : Int → Bool)
    (hr : 0<r) (hpre : t (h-1)=false) (h0 : t h=false) (h1 : t (h+1)=false)
    (run : Holds t (h+2) (List.replicate r true ++ [false])) :
    let u := put (put t (h-1) true) (h+2) false
    let out := put (clearRange u (h+3) (h+2+(r : Int))) (h+1+(r : Int)) true
    silentSegment machine (cfg 1 (h-1) t) (cfg 83 (h-2) out) (2*r+7) := by
  dsimp only
  let t1 := put t (h-1) true
  let u := put t1 (h+2) false
  have hstep := oneSeg machine _ _ (step_zero (h-1) t hpre)
  have hz : ∀ i : Nat, i<2 → t1 (h+(i : Int))=false := by
    intro i hi
    have hi' : i=0 ∨ i=1 := by omega
    rcases hi' with rfl | rfl
    · simp only [Nat.cast_zero,add_zero]
      change put t (h-1) true h=false
      rw [put_other _ _ _ _ (by omega)]
      exact h0
    · change put t (h-1) true (h+1)=false
      rw [put_other _ _ _ _ (by omega)]
      exact h1
  have hfirst : t (h+2)=true := by
    have hb := holds_get t (h+2) (List.replicate r true ++ [false]) run 0 (by simp)
    simpa [hr] using hb
  have hone : t1 (h+2)=true := by
    change put t (h-1) true (h+2)=true
    rw [put_other _ _ _ _ (by omega)]
    exact hfirst
  have h27 := scan_to_one h t1 2 hz (by simpa using hone)
  have h27' : silentSegment machine (cfg 27 h t1) (cfg 28 (h+3) u) 3 := by
    have hp : h+2+1=h+3 := by omega
    simpa only [Nat.cast_ofNat,Nat.reduceAdd,hp,u] using h27
  have hp : h-1≤(h+3)-2 := by omega
  have hm : u (h-1)=true := by
    dsimp [u,t1]
    rw [put_other _ _ _ _ (by omega)]
    simp [put]
  have hc : ∀ q, h-1<q → q<h+3 → u q=false := by
    intro q hq hq'
    have hs : q=h ∨ q=h+1 ∨ q=h+2 := by omega
    rcases hs with rfl | rfl | rfl
    · dsimp [u,t1]
      rw [put_other _ _ _ _ (by omega),put_other _ _ _ _ (by omega)]
      exact h0
    · dsimp [u,t1]
      rw [put_other _ _ _ _ (by omega),put_other _ _ _ _ (by omega)]
      exact h1
    · simp [u,put]
  have hright : ∀ q, h+3≤q → u q=t q := by
    intro q hq
    dsimp [u,t1]
    rw [put_other _ _ _ _ (by omega),put_other _ _ _ _ (by omega)]
  have hdelim : t (h+2+(r : Int))=false := by
    have hb := holds_get t (h+2) (List.replicate r true ++ [false]) run r (by simp)
    simpa using hb
  have hlast : u ((h+3)+((r-1 : Nat):Int))=false := by
    have he : h+3+((r-1 : Nat):Int)=h+2+(r : Int) := by omega
    rw [he,hright _ (by omega)]
    exact hdelim
  have hones : ∀ i : Nat, i<r-1 → u (h+3+(i : Int))=true := by
    intro i hi
    have hq : h+3≤h+3+(i : Int) := by omega
    rw [hright _ hq]
    have hb := holds_get t (h+2) (List.replicate r true ++ [false]) run (i+1) (by simp; omega)
    have he : h+2+((i+1 : Nat):Int)=h+3+(i : Int) := by push_cast; omega
    rw [he] at hb
    have hil : i+1<r := by omega
    simpa [hil] using hb
  let stop := h+1+(r : Int)
  let erased := clearRange u (h+3) (h+2+(r : Int))
  let out := put erased stop true
  have h28 := scan28_exact (r-1) (h+3) u hones hlast
  have h28' : silentSegment machine (cfg 28 (h+3) u) (cfg 6 stop erased) r := by
    have he : h+3+((r-1 : Nat):Int)=h+2+(r : Int) := by omega
    have hs : h+2+(r : Int)-1=stop := by dsimp [stop]; omega
    have ht : r-1+1=r := by omega
    simpa only [he,hs,ht,erased] using h28
  have hstop : erased stop=false := by
    by_cases hr1 : r=1
    · have he : stop=h+2 := by dsimp [stop]; omega
      rw [he]
      have hh : u (h+2)=false := by simp [u,put]
      simpa [erased,clearRange,hr1] using hh
    · have hb : h+3≤stop ∧ stop<h+2+(r : Int) := by dsimp [stop]; omega
      simp [erased,clearRange,hb]
  have h6 : silentSegment machine (cfg 6 stop erased) (cfg 97 (stop-1) out) 1 := by
    exact oneSeg machine _ _ (step6_zero stop erased hstop)
  have hmark : out (h-1)=true := by
    simp [out,erased,stop,clearRange,put,hm,show h-1≠h+1+(r : Int) by omega]
  have hcorr : ∀ q, h-1<q → q≤stop-1 → out q=false := by
    intro q hq hq'
    have hneq : q≠stop := by omega
    by_cases hleft : q<h+3
    · have hh := hc q hq hleft
      simp [out,erased,put,clearRange,hneq,show ¬(h+3≤q ∧ q<h+2+(r : Int)) by omega,hh]
    · have hb : h+3≤q ∧ q<h+2+(r : Int) := by dsimp [stop] at hq'; omega
      simp [out,erased,put,clearRange,hneq,hb]
  have h97 : silentSegment machine (cfg 97 (stop-1) out) (cfg 83 (h-2) out) (r+2) := by
    have he : stop-1-((r+1 : Nat):Int)=h-1 := by dsimp [stop]; omega
    have hs := scan97_corridor (r+1) (stop-1) (h-1) out he hmark hcorr
    have hcst : r+1+1=r+2 := by omega
    have hh : h-1-1=h-2 := by omega
    simpa only [hcst,hh] using hs
  have hstep' : silentSegment machine (cfg 1 (h-1) t) (cfg 27 h t1) 1 := by
    have hp : h-1+1=h := by omega
    simpa only [hp,t1] using hstep
  have hpreseg := segAdd machine _ _ _ 1 3 hstep' h27'
  have hs := segAdd machine _ _ _ (1+3) r hpreseg h28'
  have hs' := segAdd machine _ _ _ (1+3+r) 1 hs h6
  have hall := segAdd machine _ _ _ (1+3+r+1) (r+2) hs' h97
  have hcst : 1+3+r+1+(r+2)=2*r+7 := by omega
  simpa only [hcst,out,erased,stop,u,t1] using hall

#print axioms carry_to83_exact
end Shared.Beeping.NPcoNP.NativeUnitCarryExact83
