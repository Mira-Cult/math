import Shared.Beeping.NPcoNP.NativeHalfReturn23
import Shared.Beeping.NPcoNP.NativeHalfState1Scan
import Shared.Beeping.NPcoNP.NativeHalfState27Scan
import Shared.Beeping.NPcoNP.NativeHalfState28Exit
import Shared.Beeping.NPcoNP.NativeHalfMarkerExact
import Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
import Shared.Beeping.NPcoNP.NativeHalfZeroPrefix
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
import Shared.Beeping.NPcoNP.NativeIncBlock

/-! Exact return through the three-one carry pattern. The tape hypotheses
are local and do not assert reachability from the blank start. -/
namespace Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfReturn23
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState27Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfState28Exit
open Shared.Beeping.NPcoNP.NativeHalfMarkerExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBlock
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
attribute [local irreducible] machine

def carryTape (d : Int) (t : Int → Bool) : Int → Bool := result t (d-1) 3
def scanTape (d : Int) (t : Int → Bool) : Int → Bool := put (carryTape d t) (d+2) false
def outTape (d : Int) (r : Nat) (t : Int → Bool) : Int → Bool :=
  put (clearRange (scanTape d t) (d+3) (d+2+(r : Int))) (d+1+(r : Int)) true

/-- The specified three-one carry returns to state 83 at the exact head
position `d-5`, with a concrete output tape and no beeps. -/
theorem return_exact (d : Int) (r : Nat) (t : Int → Bool)
    (hr : 0<r)
    (c0 : t (d-4)=false) (c1 : t (d-3)=true)
    (c2 : t (d-2)=true) (c3 : t (d-1)=true)
    (z0 : t d=false) (z1 : t (d+1)=false)
    (ones : ∀ i : Nat, i<r → t (d+2+(i : Int))=true)
    (stop : t (d+2+(r : Int))=false) :
    silentSegment machine (cfg 23 (d+1+(r : Int)) t)
      (cfg 83 (d-5) (outTape d r t)) (3*r+18) ∧
    outTape d r t (d-4)=true ∧
    (∀ q, q<d-4 → outTape d r t q=t q) := by
  have hrun := holds_ones_delimiter r (d+2) t ones stop
  have hprefix : Holds t (d+2) (List.replicate r true) :=
    holds_prefix_word t (d+2) (List.replicate r true) [false] hrun
  have hword : Holds t d ([false,false] ++ List.replicate r true) := by
    simp only [List.cons_append,List.nil_append,Holds]
    refine ⟨z0,?_,?_⟩
    · simpa using z1
    · have hp : d+1+1=d+2 := by omega
      rw [hp]
      exact hprefix
  have hreverse := holds_reverse t d ([false,false] ++ List.replicate r true) hword
  have hdown : downHolds t (d+1+(r : Int)) (List.replicate r true ++ [false,false]) := by
    have hp : d+((([false,false] ++ List.replicate r true).length : Nat):Int)-1=
        d+1+(r : Int) := by simp; push_cast; omega
    rw [hp] at hreverse
    simpa [List.reverse_append] using hreverse
  obtain ⟨shape,hshape⟩ := shape_of_prefix (List.replicate r true) (prefix_ones r)
  have h23 := return_scan shape (d+1+(r : Int)) t (by rw [hshape]; exact hdown)
  rw [hshape] at h23
  have h23' : silentSegment machine (cfg 23 (d+1+(r : Int)) t) (cfg 1 (d-1) t) (r+2) := by
    simp only [List.length_replicate] at h23
    have hp : d+1+(r : Int)-(r : Int)-2=d-1 := by omega
    rw [hp] at h23
    exact h23
  have hleftword : downHolds t (d-1) (List.replicate 3 true ++ [false]) := by
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,downHolds]
    have p1 : d-1-1=d-2 := by omega
    have p2 : d-1-1-1=d-3 := by omega
    have p3 : d-1-1-1-1=d-4 := by omega
    refine ⟨c3,?_,?_,?_,trivial⟩
    · simpa only [p1] using c2
    · simpa only [p2] using c1
    · simpa only [p3] using c0
  have h1 := scan t (d-1) 3 hleftword
  have h1' : silentSegment machine (cfg 1 (d-1) t) (cfg 27 (d-3) (carryTape d t)) 4 := by
    have hp : d-1-((3 : Nat):Int)+1=d-3 := by omega
    simpa only [hp,carryTape] using h1
  have hcarryright : ∀ q, d≤q → carryTape d t q=t q := by
    intro q hq
    change put (cleared t (d-1) 3) ((d-1)-((3 : Nat):Int)) true q=t q
    rw [put_other _ _ _ _ (by omega)]
    change (if (d-1)-((3 : Nat):Int)<q ∧ q≤d-1 then false else t q)=t q
    rw [if_neg (by omega)]
  have hmark : carryTape d t (d-4)=true := by
    change (if d-4=(d-1)-((3 : Nat):Int) then true else cleared t (d-1) 3 (d-4))=true
    rw [if_pos (by omega)]
  have hzeros : ∀ i : Nat, i<5 → carryTape d t (d-3+(i : Int))=false := by
    intro i hi
    by_cases hright : d≤d-3+(i : Int)
    · rw [hcarryright _ hright]
      have hc : d-3+(i : Int)=d ∨ d-3+(i : Int)=d+1 := by omega
      rcases hc with hp | hp
      · rw [hp]; exact z0
      · rw [hp]; exact z1
    · change put (cleared t (d-1) 3) ((d-1)-((3 : Nat):Int)) true (d-3+(i : Int))=false
      rw [put_other _ _ _ _ (by omega)]
      change (if (d-1)-((3 : Nat):Int)<d-3+(i : Int) ∧ d-3+(i : Int)≤d-1
        then false else t (d-3+(i : Int)))=false
      rw [if_pos (by omega)]
  have hone : carryTape d t (d+2)=true := by
    rw [hcarryright _ (by omega)]
    simpa using ones 0 hr
  have h27 := scan_to_one (d-3) (carryTape d t) 5 hzeros (by
    have hp : d-3+((5 : Nat):Int)=d+2 := by omega
    rw [hp]
    exact hone)
  have h27' : silentSegment machine (cfg 27 (d-3) (carryTape d t))
      (cfg 28 (d+3) (scanTape d t)) 6 := by
    have hp : d-3+5+1=d+3 := by omega
    have hp' : d-3+5=d+2 := by omega
    have hp'' : d+2+1=d+3 := by omega
    simpa only [Nat.cast_ofNat,hp,hp',hp'',scanTape] using h27
  have hscanright : ∀ q, d+3≤q → scanTape d t q=t q := by
    intro q hq
    change put (carryTape d t) (d+2) false q=t q
    rw [put_other _ _ _ _ (by omega),hcarryright _ (by omega)]
  have hscanmark : scanTape d t (d-4)=true := by
    change put (carryTape d t) (d+2) false (d-4)=true
    rw [put_other _ _ _ _ (by omega)]
    exact hmark
  have hscanzeros : ∀ q, d-4<q → q<d+3 → scanTape d t q=false := by
    intro q hq hq'
    by_cases he : q=d+2
    · subst q
      simp [scanTape,put]
    · change put (carryTape d t) (d+2) false q=false
      rw [put_other _ _ _ _ he]
      let i := (q-(d-3)).toNat
      have hi : (i : Int)=q-(d-3) := Int.toNat_of_nonneg (by omega)
      have hbound : i<5 := by omega
      have hp : d-3+(i : Int)=q := by omega
      rw [← hp]
      exact hzeros i hbound
  have h28ones : ∀ i : Nat, i<r-1 → scanTape d t (d+3+(i : Int))=true := by
    intro i hi
    rw [hscanright _ (by omega)]
    have hp : d+3+(i : Int)=d+2+((i+1 : Nat):Int) := by push_cast; omega
    rw [hp]
    exact ones (i+1) (by omega)
  have h28stop : scanTape d t (d+3+((r-1 : Nat):Int))=false := by
    have hp : d+3+((r-1 : Nat):Int)=d+2+(r : Int) := by omega
    rw [hp,hscanright _ (by omega)]
    exact stop
  let erased := clearRange (scanTape d t) (d+3) (d+2+(r : Int))
  let p := d+1+(r : Int)
  have h28 := scan28_exact (r-1) (d+3) (scanTape d t) h28ones h28stop
  have h28' : silentSegment machine (cfg 28 (d+3) (scanTape d t))
      (cfg 6 p erased) r := by
    have he : d+3+((r-1 : Nat):Int)=d+2+(r : Int) := by omega
    have hp : d+2+(r : Int)-1=p := by dsimp [p]; omega
    have hc : r-1+1=r := by omega
    simpa only [he,hp,hc,erased] using h28
  have hpzero : erased p=false := by
    by_cases h : r=1
    · have hp : p=d+2 := by dsimp [p]; omega
      rw [hp]
      simp [erased,clearRange,scanTape,put,h]
    · have hc : d+3≤p ∧ p<d+2+(r : Int) := by dsimp [p]; omega
      simp [erased,clearRange,hc]
  have h6 : silentSegment machine (cfg 6 p erased)
      (cfg 97 (p-1) (outTape d r t)) 1 := by
    simpa only [outTape,erased,p] using oneSeg machine _ _ (step6_zero p erased hpzero)
  have houtmark : outTape d r t (d-4)=true := by
    change put erased p true (d-4)=true
    rw [put_other _ _ _ _ (by dsimp [p]; omega)]
    change (if d+3≤d-4 ∧ d-4<d+2+(r : Int) then false else scanTape d t (d-4))=true
    rw [if_neg (by omega)]
    exact hscanmark
  have houtzeros : ∀ q, d-4<q → q≤p-1 → outTape d r t q=false := by
    intro q hq hq'
    change put erased p true q=false
    rw [put_other _ _ _ _ (by omega)]
    by_cases hl : q<d+3
    · change (if d+3≤q ∧ q<d+2+(r : Int) then false else scanTape d t q)=false
      rw [if_neg (by omega)]
      exact hscanzeros q hq hl
    · change (if d+3≤q ∧ q<d+2+(r : Int) then false else scanTape d t q)=false
      rw [if_pos (by dsimp [p] at hq'; omega)]
  have h97 := scan97_corridor (r+4) (p-1) (d-4) (outTape d r t)
    (by dsimp [p]; push_cast; omega) houtmark houtzeros
  have h97' : silentSegment machine (cfg 97 (p-1) (outTape d r t))
      (cfg 83 (d-5) (outTape d r t)) (r+5) := by
    have hp : d-4-1=d-5 := by omega
    have hc : r+4+1=r+5 := by omega
    simpa only [hp,hc] using h97
  have ha := segAdd machine _ _ _ (r+2) 4 h23' h1'
  have hb := segAdd machine _ _ _ (r+2+4) 6 ha h27'
  have hc := segAdd machine _ _ _ (r+2+4+6) r hb h28'
  have hd := segAdd machine _ _ _ (r+2+4+6+r) 1 hc h6
  have hall := segAdd machine _ _ _ (r+2+4+6+r+1) (r+5) hd h97'
  have hcost : r+2+4+6+r+1+(r+5)=3*r+18 := by omega
  refine ⟨by simpa only [hcost] using hall,houtmark,?_⟩
  intro q hq
  change put erased p true q=t q
  rw [put_other _ _ _ _ (by dsimp [p]; omega)]
  change (if d+3≤q ∧ q<d+2+(r : Int) then false else scanTape d t q)=t q
  rw [if_neg (by omega)]
  change put (carryTape d t) (d+2) false q=t q
  rw [put_other _ _ _ _ (by omega)]
  change put (cleared t (d-1) 3) ((d-1)-((3 : Nat):Int)) true q=t q
  rw [put_other _ _ _ _ (by omega)]
  change (if (d-1)-((3 : Nat):Int)<q ∧ q≤d-1 then false else t q)=t q
  rw [if_neg (by omega)]

#print axioms return_exact
end Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
