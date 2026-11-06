import Shared.Beeping.NPcoNP.NativeUnitCarryExact83
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue

/-! Control-position refinement for the positive selector's local return.
The hypotheses are supplied physical tape words, not a reachability claim. -/
namespace Shared.Beeping.NPcoNP.NativePositiveControlReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState27Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfMarkerExact
open Shared.Beeping.NPcoNP.NativeHalfReturn23
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeIncReturn23
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- A three-one carry block followed by a zero pair and a nonempty one-run
forces the literal state-23 return to state 83 exactly five cells left of the
pair. The output tape is the stated carry, first-one consumption, clearing,
and replacement; its left prefix is unchanged. -/
theorem positive_control_return (d : Int) (r : Nat) (t : Int → Bool)
    (hr : 0<r)
    (carry : downHolds t (d-1) (List.replicate 3 true ++ [false]))
    (h0 : t d=false) (h1 : t (d+1)=false)
    (run : Holds t (d+2) (List.replicate r true ++ [false])) :
    let mid := result t (d-1) 3
    let u := put mid (d+2) false
    ∃ (n : Nat) (stop : Int) (out : Int → Bool), 0<n ∧ stop=d+(r : Int)+1 ∧
      out (d-4)=true ∧
      out=put (clearRange u (d+3) (stop+1)) stop true ∧
      (∀ q, q<d-4 → out q=t q) ∧
      (∀ q, d+(r : Int)+2≤q → out q=t q) ∧
      silentSegment machine (cfg 23 (d+((r : Nat):Int)+1) t)
        (cfg 83 (d-5) out) n := by
  dsimp only
  let mid := result t (d-1) 3
  let u := put mid (d+2) false
  have hword : Holds t (d+2) (List.replicate r true) :=
    holds_prefix_word t _ _ [false] run
  have hrev := holds_reverse t (d+2) (List.replicate r true) hword
  have hrev' : downHolds t (d+(r : Int)+1) (List.replicate r true) := by
    have he : d+2+(r : Int)-1=d+(r : Int)+1 := by omega
    simpa [List.reverse_replicate,he] using hrev
  have hpair : downHolds t (d+1) [false,false] := by
    change t (d+1)=false ∧ t (d+1-1)=false ∧ True
    exact ⟨h1,by simpa using h0,trivial⟩
  have hjoined : downHolds t (d+(r : Int)+1) (List.replicate r true ++ [false,false]) := by
    apply down_append t _ _ _ hrev'
    have hp : d+(r : Int)+1-((List.replicate r true).length : Int)=d+1 := by simp; omega
    rw [hp]
    exact hpair
  obtain ⟨shape,hshape⟩ := shape_of_prefix (List.replicate r true) (prefix_ones r)
  rw [←hshape] at hjoined
  have hret := return_scan shape (d+(r : Int)+1) t hjoined
  have hret' : silentSegment machine (cfg 23 (d+(r : Int)+1) t) (cfg 1 (d-1) t) (r+2) := by
    have hs : (bits shape).length=r := by rw [hshape]; simp
    have he : d+(r : Int)+1-(r : Int)-2=d-1 := by omega
    simpa [hs,he] using hret
  have hcarry := scan t (d-1) 3 carry
  have hcarry' : silentSegment machine (cfg 1 (d-1) t) (cfg 27 (d-3) mid) 4 := by
    have he : d-1-(3:Int)+1=d-3 := by omega
    simpa only [Nat.cast_ofNat,Nat.reduceAdd,he,mid] using hcarry
  have hmidbelow : ∀ q, q<d-4 → mid q=t q := by
    intro q hq
    change put (cleared t (d-1) 3) (d-1-3) true q=t q
    rw [put_other _ _ _ _ (by omega)]
    change (if d-1-3<q ∧ q≤d-1 then false else t q)=t q
    rw [if_neg (by omega)]
  have hmidabove : ∀ q, d≤q → mid q=t q := by
    intro q hq
    change put (cleared t (d-1) 3) (d-1-3) true q=t q
    rw [put_other _ _ _ _ (by omega)]
    change (if d-1-3<q ∧ q≤d-1 then false else t q)=t q
    rw [if_neg (by omega)]
  have hmidcleared : ∀ q, d-3≤q → q≤d-1 → mid q=false := by
    intro q hq hq'
    change put (cleared t (d-1) 3) (d-1-3) true q=false
    rw [put_other _ _ _ _ (by omega)]
    change (if d-1-3<q ∧ q≤d-1 then false else t q)=false
    rw [if_pos (by omega)]
  have hmark : u (d-4)=true := by
    change put mid (d+2) false (d-4)=true
    rw [put_other _ _ _ _ (by omega)]
    change put (cleared t (d-1) 3) (d-1-3) true (d-4)=true
    have he : d-4=d-1-3 := by omega
    simp [put,he]
  have hmidzero : ∀ i : Nat, i<5 → mid ((d-3)+(i : Int))=false := by
    intro i hi
    by_cases hs : i<3
    · apply hmidcleared <;> omega
    · have hi' : i=3 ∨ i=4 := by omega
      rcases hi' with rfl | rfl
      · norm_num only [Nat.cast_ofNat]
        have he : d-3+(3:Int)=d := by omega
        rw [he,hmidabove _ (by omega)]
        exact h0
      · norm_num only [Nat.cast_ofNat]
        have he : d-3+(4:Int)=d+1 := by omega
        rw [he,hmidabove _ (by omega)]
        exact h1
  have hfirst : t (d+2)=true := by
    have hh := holds_get t (d+2) (List.replicate r true ++ [false]) run 0 (by simp)
    simpa [hr] using hh
  have hfirst' : mid ((d-3)+5)=true := by
    have he : (d-3)+5=d+2 := by omega
    rw [he,hmidabove _ (by omega)]
    exact hfirst
  have h27 := scan_to_one (d-3) mid 5 hmidzero hfirst'
  have h27' : silentSegment machine (cfg 27 (d-3) mid) (cfg 28 (d+3) u) 6 := by
    have he : d-3+(5:Int)=d+2 := by omega
    have he' : d+2+1=d+3 := by omega
    simpa only [Nat.cast_ofNat,Nat.reduceAdd,he,he',u] using h27
  have hcorr : ∀ q, d-4<q → q<d+3 → u q=false := by
    intro q hq hq'
    by_cases he : q=d+2
    · subst q; simp [u,put]
    · have hl : d-3≤q := by omega
      have hu : q<d+2 := by omega
      let i := (q-(d-3)).toNat
      have hi : (i : Int)=q-(d-3) := Int.toNat_of_nonneg (by omega)
      have hip : i<5 := by omega
      have hv := hmidzero i hip
      have hp : d-3+(i : Int)=q := by omega
      rw [hp] at hv
      change put mid (d+2) false q=false
      rw [put_other _ _ _ _ he]
      exact hv
  have hdelim : t (d+2+(r : Int))=false := by
    have hh := holds_get t (d+2) (List.replicate r true ++ [false]) run r (by simp)
    simpa using hh
  have hz : u ((d+3)+((r-1 : Nat):Int))=false := by
    have hp : d+3+((r-1 : Nat):Int)=d+2+(r : Int) := by omega
    rw [hp]
    change put mid (d+2) false (d+2+(r : Int))=false
    rw [put_other _ _ _ _ (by omega),hmidabove _ (by omega)]
    exact hdelim
  obtain ⟨m,stop,out,hm,hstop,hout,hzero,hones,heq,hprefix,hfinal⟩ :=
    state28_to83_exact (d+3) (d-4) u (by omega) hmark hcorr (r-1) hz
  have hup : ∀ q, d+3≤q → u q=t q := by
    intro q hq
    change put mid (d+2) false q=t q
    rw [put_other _ _ _ _ (by omega),hmidabove q (by omega)]
  have hupper : stop<d+2+(r : Int) := by
    by_contra hn
    have ho := hones (d+2+(r : Int)) (by omega) (by omega)
    rw [hup _ (by omega),hdelim] at ho
    contradiction
  have hlower : d+(r : Int)+1≤stop := by
    by_contra hn
    let i := (stop+1-(d+2)).toNat
    have hi : (i : Int)=stop+1-(d+2) := Int.toNat_of_nonneg (by omega)
    have hir : i<r := by omega
    have hindex : i<(List.replicate r true ++ [false]).length := by simp; omega
    have ho := holds_get t (d+2) _ run i hindex
    have hb : (List.replicate r true ++ [false])[i]'hindex=true := by
      rw [List.getElem_append_left (by simpa using hir)]
      simp
    rw [hb] at ho
    have hp : d+2+(i : Int)=stop+1 := by omega
    rw [hp] at ho
    rw [hup _ (by omega)] at hzero
    rw [hzero] at ho
    contradiction
  have hstopEq : stop=d+(r : Int)+1 := by omega
  have hright : ∀ q, d+(r : Int)+2≤q → out q=t q := by
    intro q hq
    rw [heq,put_other _ _ _ _ (by omega)]
    change (if d+3≤q ∧ q<stop+1 then false else u q)=t q
    rw [if_neg (by omega)]
    exact hup q (by omega)
  have hleft : ∀ q, q<d-4 → out q=t q := by
    intro q hq
    rw [hprefix q (by omega)]
    change put mid (d+2) false q=t q
    rw [put_other _ _ _ _ (by omega),hmidbelow q hq]
  have hpre := segAdd machine _ _ _ (r+2) 4 hret' hcarry'
  have hpre' := segAdd machine _ _ _ (r+2+4) 6 hpre h27'
  have hall := segAdd machine _ _ _ (r+2+4+6) m hpre' hfinal
  have he : d-4-1=d-5 := by omega
  exact ⟨r+2+4+6+m,stop,out,by omega,hstopEq,hout,heq,hleft,hright,by simpa only [he] using hall⟩

#print axioms positive_control_return
end Shared.Beeping.NPcoNP.NativePositiveControlReturn
