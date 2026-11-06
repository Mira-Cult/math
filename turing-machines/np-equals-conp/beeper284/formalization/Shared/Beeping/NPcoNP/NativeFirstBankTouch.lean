import Shared.Beeping.NPcoNP.Native279BankScan

/-! Connect the first paid beep and zero-branch fill to the next literal bank
scan. The six-block position is physical; mapping it to a graph register and
the later completion of the operation remain separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeFirstBankTouch
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeFirstZeroNext
open Shared.Beeping.NPcoNP.Native279BankScan
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Under a specified first-event layout and an initial contiguous control
run, the complete paid physical segment reaches state 262 after clearing the
first bit of the sixth physical bank block. The exact remaining block word,
bank frame, head position, and single-event word are retained. -/
theorem supplied_beep_to262_full (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+7≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false)
    (values : List Nat) (value : Nat) (tail : List Bool)
    (hlen : values.length=5)
    (bank : Holds t (separator+1) (encode values ++ (block value ++ tail))) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      let pos := separator+1+((encode values).length : Int)
      (∃ mid stop, h+6≤stop ∧ stop+1=separator ∧ mid stop=true ∧
        Holds mid (h-4) [true,true,false,true,false,false] ∧
        (∀ q, q<h-4 → mid q=false) ∧
        (∀ q, h≤q → q<stop → mid q=false) ∧
        out=clearAt pos (fillRange (setAt (h+2) mid) (h+5) stop)) ∧
      Holds out pos (false :: (List.replicate value true ++ false :: tail)) ∧
      (∀ q, separator≤q → q≠pos → out q=t q) ∧
      physical.advance (cfg 99 h t) n=cfg 262 (pos-2) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  have hshort : ∀ q, h+3≤q → q≤h+6 → t q=true := by
    intro q hq hq'
    exact ones q hq (by omega)
  obtain ⟨n,mid,stop,hn,hstop,hsep,hstopNext,hmark,hmidWord,hmidLeft,hclear,hframe,ha,hw⟩ :=
    supplied_beep_to279_full h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hshort left hb right (by omega) hsepzero
  have he : stop+1=separator := by
    by_contra he'
    have hh := ones (stop+1) (by omega) (by omega)
    rw [hstopNext] at hh
    contradiction
  let u := fillRange (setAt (h+2) mid) (h+5) stop
  let k := (separator-(h+5)).toNat
  have hk : (k : Int)=separator-(h+5) := Int.toNat_of_nonneg (by omega)
  have hp : h+5+(k : Int)=separator := by omega
  have h0 : u (h+3)=false := by
    have hno : ¬ (h+5≤h+3 ∧ h+3<stop) := by omega
    simp [u,fillRange,setAt,hno,show h+3≠h+2 by omega,hclear (h+3) (by omega) (by omega)]
  have h1 : u (h+4)=false := by
    have hno : ¬ (h+5≤h+4 ∧ h+4<stop) := by omega
    simp [u,fillRange,setAt,hno,show h+4≠h+2 by omega,hclear (h+4) (by omega) (by omega)]
  have hcontrol : ∀ i : Nat, i<k → u ((h+3)+2+(i : Int))=true := by
    intro i hi
    let q := h+5+(i : Int)
    have hq : h+5≤q ∧ q≤stop := by dsimp [q]; omega
    by_cases hs : q<stop
    · have hrange : h+5≤q ∧ q<stop := ⟨hq.1,hs⟩
      simpa [u,fillRange,q,hrange,Int.add_assoc] using (show u q=true by simp [u,fillRange,hrange])
    · have hqeq : q=stop := by omega
      subst q
      have hno : ¬ (h+5≤stop ∧ stop<stop) := by omega
      have hu : u stop=true := by simp [u,fillRange,setAt,hno,show stop≠h+2 by omega,hmark]
      have hpos : h+3+2+(i : Int)=stop := by omega
      simpa only [hpos] using hu
  have hdelim : u ((h+3)+2+(k : Int))=false := by
    have heq : h+3+2+(k : Int)=separator := by omega
    rw [heq]
    change fillRange (setAt (h+2) mid) (h+5) stop separator=false
    rw [hframe separator (le_refl _)]
    exact hsepzero
  have hbank : Holds u (separator+1) (encode values ++ (block value ++ tail)) := by
    apply holds_transport t u (separator+1) _ bank
    intro q hq _
    exact (hframe q (by omega)).symm
  have hbank' : Holds u ((h+3)+3+(k : Int)) (encode values ++ (block value ++ tail)) := by
    have heq : h+3+3+(k : Int)=separator+1 := by omega
    simpa only [heq] using hbank
  have h1' : u (h+3+1)=false := by
    have hx : h+3+1=h+4 := by omega
    simpa only [hx] using h1
  obtain ⟨_hscanFrame,hscan⟩ := scan279_to262 (h+3) u k values value tail hlen h0 h1' hcontrol hdelim hbank'
  let pos := separator+1+((encode values).length : Int)
  have hpos : h+3+3+(k : Int)+((encode values).length : Int)=pos := by dsimp [pos]; omega
  have hscan' : silentSegment machine (cfg 279 (h+3) u) (cfg 262 (pos-2) (clearAt pos u))
      (k+(encode values).length+5) := by simpa only [hpos] using hscan
  have ha' : physical.advance (cfg 99 h t) n=cfg 279 (h+3) u := by simpa [u] using ha
  obtain ⟨ha'',hw''⟩ := append_silent _ _ _ n (k+(encode values).length+5) ha' hw hscan'
  have htarget := holds_append_tail u (separator+1) (encode values) (block value ++ tail) hbank
  have htarget' : Holds u pos (true :: (List.replicate value true ++ false :: tail)) := by
    simpa [pos,block,List.replicate_succ,List.append_assoc] using htarget
  have htail : Holds (clearAt pos u) (pos+1) (List.replicate value true ++ false :: tail) :=
    holds_clear_left u pos (pos+1) _ (by omega) htarget'.2
  refine ⟨n+(k+(encode values).length+5),clearAt pos u,by omega,
    ⟨mid,stop,hstop,he,hmark,hmidWord,hmidLeft,hclear,rfl⟩,?_,?_,ha'',hw''⟩
  · change Holds (clearAt pos u) pos (false :: (List.replicate value true ++ false :: tail))
    exact ⟨by simp [clearAt],htail⟩
  · intro q hq hne
    change (if q=pos then false else u q)=t q
    rw [if_neg hne]
    simpa only [u] using hframe q hq

/-- The earlier bank-touch contract remains available. -/
theorem supplied_beep_to262 (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+7≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false)
    (values : List Nat) (value : Nat) (tail : List Bool)
    (hlen : values.length=5)
    (bank : Holds t (separator+1) (encode values ++ (block value ++ tail))) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      let pos := separator+1+((encode values).length : Int)
      (∃ mid stop, h+6≤stop ∧ stop+1=separator ∧ mid stop=true ∧
        (∀ q, h≤q → q<stop → mid q=false) ∧
        out=clearAt pos (fillRange (setAt (h+2) mid) (h+5) stop)) ∧
      Holds out pos (false :: (List.replicate value true ++ false :: tail)) ∧
      (∀ q, separator≤q → q≠pos → out q=t q) ∧
      physical.advance (cfg 99 h t) n=cfg 262 (pos-2) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,out,hn,⟨mid,stop,hs,hsep,hm,_hw,_hl,hc,he⟩,hword,hframe,ha,hw⟩ :=
    supplied_beep_to262_full h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2 hlong ones left
      hb right hsepzero values value tail hlen bank
  exact ⟨n,out,hn,⟨mid,stop,hs,hsep,hm,hc,he⟩,hword,hframe,ha,hw⟩

#print axioms supplied_beep_to262_full
#print axioms supplied_beep_to262
end Shared.Beeping.NPcoNP.NativeFirstBankTouch
