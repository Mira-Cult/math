import Shared.Beeping.NPcoNP.NativeFourthReturn25
import Shared.Beeping.NPcoNP.NativeCarryReturn83
import Shared.Beeping.NPcoNP.NativeHalfSelectorBound
import Shared.Beeping.NPcoNP.NativeHalfMarkerRetain
import Shared.Beeping.NPcoNP.NativeFirstDispatch

/-! Generic finite carry/selector progress for the literal table. This proves
no parser or graph-control correspondence. -/
namespace Shared.Beeping.NPcoNP.NativeCarrySelectorGeneric
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorBound
open Shared.Beeping.NPcoNP.NativeHalfMarkerRetain
open Shared.Beeping.NPcoNP.NativeCarryReturn83
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeFourthReturn25
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Given a finite left-zero cutoff and a marker immediately right of state
83, the selector terminates silently. The first one encountered by state 92,
all earlier zeros and a quantitative bound are explicit. -/
theorem selector_to93_first_one (t : Int → Bool) (h : Int) (k : Nat)
    (left : ∀ j : Nat, k≤j → t (h-(j : Int))=false)
    (marker : t (h+1)=true) :
    ∃ n j : Nat, 14≤n ∧ n≤k+14 ∧ j≤n+1 ∧
      (∀ i : Nat, i<j → t (h-(n : Int)+(i : Int))=false) ∧
      t (h-(n : Int)+(j : Int))=true ∧
      silentSegment machine (cfg 83 h t)
        (cfg 93 (h-(n : Int)+(j : Int)+1) t) (n+j+1) := by
  obtain ⟨n,hn,hbound,hscan⟩ := selector_progress_bound t h k left
  have hp : h-(n : Int)≤h+1 := by omega
  obtain ⟨j,hzeros,hone⟩ := first_one (h-(n : Int)) (h+1) t hp marker
  have hj : j≤n+1 := by
    by_contra hnot
    have hz := hzeros (n+1) (by omega)
    have he : h-(n : Int)+((n+1 : Nat) : Int)=h+1 := by push_cast; omega
    rw [he,marker] at hz
    contradiction
  have hnext := scan92_exact j (h-(n : Int)) t hzeros hone
  have hall := segAdd machine _ _ _ n (j+1) hscan hnext
  refine ⟨n,j,hn,hbound,hj,hzeros,hone,?_⟩
  simpa [Nat.add_assoc] using hall

/-- The selector's total finite silent duration is bounded by `2*k+30`,
without assuming that the supplied tape is reachable. -/
theorem selector_to93_bound (t : Int → Bool) (h : Int) (k : Nat)
    (left : ∀ j : Nat, k≤j → t (h-(j : Int))=false)
    (marker : t (h+1)=true) :
    ∃ (steps : Nat) (head : Int), 15≤steps ∧ steps≤2*k+30 ∧
      t (head-1)=true ∧ silentSegment machine (cfg 83 h t) (cfg 93 head t) steps := by
  obtain ⟨n,j,hn,hb,hj,_hz,hone,hs⟩ := selector_to93_first_one t h k left marker
  let head := h-(n : Int)+(j : Int)+1
  have hh : t (head-1)=true := by
    have he : head-1=h-(n : Int)+(j : Int) := by dsimp [head]; omega
    simpa only [he] using hone
  exact ⟨n+j+1,head,by omega,by omega,hh,hs⟩

/-- A finite left blank tail, finite right blank tail and a one to the right
of a state-1 head force a finite positive silent segment to state 93. The
carry marker and its protected prefix are retained, and the state-93 head is
immediately to the right of a one. -/
theorem carry_selector_progress (h p z b : Int) (t : Int → Bool)
    (left : ∀ q, q≤z → t q=false) (right : ∀ q, b≤q → t q=false)
    (hp : h<p) (hone : t p=true) :
    ∃ (steps : Nat) (out : Int → Bool) (mark finalHead : Int), 0<steps ∧
      mark≤h ∧ out mark=true ∧ (∀ q, q<mark → out q=t q) ∧
      out (finalHead-1)=true ∧
      silentSegment machine (cfg 1 h t) (cfg 93 finalHead out) steps := by
  obtain ⟨j,l,n,stop,out,hn,_hhead,_hstop,hmark,_hzero,_hones,_heq,hprefix,hcarry⟩ :=
    carry_to83 h p z b t left right hp hone
  let mark := h-(j : Int)
  let h83 := mark-1
  let z' := min z (mark-1)
  let k := (h83-z').toNat
  have hz' : z'≤h83 := by dsimp [z',h83]; omega
  have hk : (k : Int)=h83-z' := Int.toNat_of_nonneg (by omega)
  have hblank : ∀ i : Nat, k ≤ i → out (h83-(i : Int))=false := by
    intro i hi
    have hq : h83-(i : Int)≤z' := by omega
    have hqmark : h83-(i : Int)<mark := by dsimp [z'] at hq; omega
    rw [hprefix _ hqmark]
    apply left
    dsimp [z'] at hq
    omega
  have hmarker : out (h83+1)=true := by
    have he : h83+1=mark := by dsimp [h83]; omega
    simpa only [he,mark] using hmark
  obtain ⟨a,d,ha,_hb,_hd,_hzeros,hone',hselector⟩ :=
    selector_to93_first_one out h83 k hblank hmarker
  let finalHead := h83-(a : Int)+(d : Int)+1
  have hleftOne : out (finalHead-1)=true := by
    have he : finalHead-1=h83-(a : Int)+(d : Int) := by dsimp [finalHead]; omega
    simpa only [he] using hone'
  have hall := segAdd machine _ _ _ ((j+1)+(l+1)+n) (a+d+1) hcarry hselector
  refine ⟨(j+1)+(l+1)+n+(a+d+1),out,mark,finalHead,by omega,?_,?_,?_,hleftOne,?_⟩
  · dsimp [mark]; omega
  · simpa only [mark] using hmark
  · simpa only [mark] using hprefix
  · simpa only [mark,h83,finalHead] using hall

/-- The supplied first-event layout has a finite continuation through the
next carry and selector, retaining exactly the one event. The resulting
state-93 position is not yet identified with a grammar path. -/
theorem supplied_beep_fourth_carry_selector (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+11≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false) (tail : List Bool)
    (bank : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail))) :
    ∃ (n : Nat) (out : Int → Bool) (head : Int), 1<n ∧ out (head-1)=true ∧
      physical.advance (cfg 99 h t) n=cfg 93 head out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,mid,hn,_hpath,hleft,_h5,_h6,_h7,hcontrol,hframe,_hbank,ha,hw⟩ :=
    supplied_beep_fourth_return h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hlong ones left hb right hsepzero tail bank
  let bound := max b separator
  have hr : ∀ q, bound≤q → mid q=false := by
    intro q hq
    rw [hframe q (le_trans (le_max_right _ _) hq)]
    exact right q (le_trans (le_max_left _ _) hq)
  have hl : ∀ q, q≤h-5 → mid q=false := by
    intro q hq
    exact hleft q (by omega)
  have hp : mid (h+8)=true := hcontrol (h+8) (by omega) (by omega)
  obtain ⟨m,out,_mark,head,hm,_hle,_hmark,_hprefix,hhead,hseg⟩ :=
    carry_selector_progress (h+4) (h+8) (h-5) bound mid hl hr (by omega) hp
  obtain ⟨ha',hw'⟩ := append_silent _ _ _ n m ha hw hseg
  exact ⟨n+m,out,head,by omega,hhead,ha',hw'⟩

#print axioms selector_to93_bound
#print axioms selector_to93_first_one
#print axioms carry_selector_progress
#print axioms supplied_beep_fourth_carry_selector
end Shared.Beeping.NPcoNP.NativeCarrySelectorGeneric
