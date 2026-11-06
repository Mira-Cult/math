import Shared.Beeping.NPcoNP.NativeUnit261Return1
import Shared.Beeping.NPcoNP.NativeHalfMarkerExact
import Shared.Beeping.NPcoNP.NativeHalfState27Scan

/-! A parameterized finite return from the unit-dispatch control boundary
to state 83, with an exact output tape and explicit layout hypotheses. -/
namespace Shared.Beeping.NPcoNP.NativeUnitCarry83
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState27Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfMarkerExact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- With a zero at the state-1 head, two following zeros, and a nonempty
one-run with its delimiter, the literal table reaches state 83 in positive
finite silent time. Its complete output tape is specified. -/
theorem carry_to83 (r : Nat) (h : Int) (t : Int → Bool)
    (hr : 0<r) (hpre : t (h-1)=false) (h0 : t h=false) (h1 : t (h+1)=false)
    (run : Holds t (h+2) (List.replicate r true ++ [false])) :
    let u := put (put t (h-1) true) (h+2) false
    let out := put (clearRange u (h+3) (h+2+(r : Int))) (h+1+(r : Int)) true
    ∃ n : Nat, 0<n ∧ silentSegment machine (cfg 1 (h-1) t) (cfg 83 (h-2) out) n := by
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
  obtain ⟨n,stop,out,hn,hstop,_hmark,hstopzero,hstopones,hexact,_hprefix,hret⟩ :=
    state28_to83_exact (h+3) (h-1) u hp hm hc (r-1) hlast
  have hrun : ∀ q, h+3≤q → q≤h+1+(r : Int) → u q=true := by
    intro q hq hq'
    let i := (q-(h+2)).toNat
    have hi : (i : Int)=q-(h+2) := Int.toNat_of_nonneg (by omega)
    have hir : i<r := by omega
    rw [hright q hq]
    have hb := holds_get t (h+2) (List.replicate r true ++ [false]) run i (by simp; omega)
    have he : h+2+(i : Int)=q := by omega
    rw [he] at hb
    simpa [hir] using hb
  have hdelimiter : u (h+2+(r : Int))=false := by
    rw [hright _ (by omega)]
    exact hdelim
  have hstopExact : stop=h+1+(r : Int) := by
    by_contra hne
    by_cases hl : stop<h+1+(r : Int)
    · have ht := hrun (stop+1) (by omega) (by omega)
      rw [hstopzero] at ht
      contradiction
    · have ht := hstopones (h+2+(r : Int)) (by omega) (by omega)
      rw [hdelimiter] at ht
      contradiction
  have hout : out=put (clearRange u (h+3) (h+2+(r : Int))) (h+1+(r : Int)) true := by
    rw [hexact,hstopExact]
    congr 2 <;> omega
  rw [hout] at hret
  have hstep' : silentSegment machine (cfg 1 (h-1) t) (cfg 27 h t1) 1 := by
    have hp : h-1+1=h := by omega
    simpa only [hp,t1] using hstep
  have hpreseg := segAdd machine _ _ _ 1 3 hstep' h27'
  have hall := segAdd machine _ _ _ (1+3) n hpreseg hret
  refine ⟨1+3+n,by omega,?_⟩
  have hp : h-1-1=h-2 := by omega
  simpa only [u,t1,hp] using hall

#print axioms carry_to83
end Shared.Beeping.NPcoNP.NativeUnitCarry83
