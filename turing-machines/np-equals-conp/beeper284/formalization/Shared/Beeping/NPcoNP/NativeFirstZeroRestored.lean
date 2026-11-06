import Shared.Beeping.NPcoNP.NativeZeroRestoreWindow

/-! Connect the first physical bank touch to the paid zero-block restoration.
The supplied initial layout and the state-25 boundary are explicit; no
whole-run or graph-control relation is asserted. -/
namespace Shared.Beeping.NPcoNP.NativeFirstZeroRestored
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeFirstBankTouch
open Shared.Beeping.NPcoNP.NativeZeroRestore
open Shared.Beeping.NPcoNP.NativeZeroRestoreWindow
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Starting from the supplied first-beep layout with six zero-valued leading
blocks, the machine silently restores the temporarily cleared bit and reaches
state 25. Every cell at or beyond the separator equals its event-time value,
and the complete physical event word is exactly one beep. -/
theorem supplied_beep_zero_restored_full (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+7≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false) (tail : List Bool)
    (bank : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail))) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      Holds out (h-4) [true,true,false,true,false,false,false,false,true] ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+4≤q → q<separator → out q=true) ∧
      (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) ∧
      physical.advance (cfg 99 h t) n=cfg 25 (separator+10) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,touched,hn,⟨mid,stop,hstop,hstopSep,hmark,hmidWord,hmidLeft,hclear,htape⟩,
      hword,hframe,ha,hw⟩ :=
    supplied_beep_to262_full h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2 hlong ones left
      hb right hsepzero (List.replicate 5 0) 0 tail (by decide) bank
  have hlen : (encode (List.replicate 5 0)).length=10 := by decide
  have hpos : separator+1+((encode (List.replicate 5 0)).length : Int)=separator+11 := by rw [hlen]; omega
  have hhead : separator+1+((encode (List.replicate 5 0)).length : Int)-2=separator+9 := by rw [hlen]; omega
  have htape' : touched=clearAt (separator+11) (fillRange (setAt (h+2) mid) (h+5) stop) := by
    simpa only [hpos] using htape
  have hword' : Holds touched (separator+11) (false::false::tail) := by
    simpa only [hpos,List.replicate_zero,List.nil_append] using hword
  have hframe' : ∀ q, separator≤q → q≠separator+11 → touched q=t q := by
    intro q hq hne
    apply hframe q hq
    simpa only [hpos] using hne
  have hmark' : touched (h+2)=true := by
    rw [htape']
    have hno : ¬ (h+5≤h+2 ∧ h+2<stop) := by omega
    simp [clearAt,fillRange,setAt,hno,show h+2≠separator+11 by omega]
  have hz1 : touched (h+3)=false := by
    rw [htape']
    have hm : mid (h+3)=false := hclear (h+3) (by omega) (by omega)
    simp [clearAt,fillRange,setAt,show h+3≠separator+11 by omega,
      show h+3≠h+2 by omega,hm]
  have hz2 : touched (h+4)=false := by
    rw [htape']
    have hm : mid (h+4)=false := hclear (h+4) (by omega) (by omega)
    simp [clearAt,fillRange,setAt,show h+4≠separator+11 by omega,
      show h+4≠h+2 by omega,hm]
  have hones : ∀ q, h+5≤q → q<separator → touched q=true := by
    intro q hq hq'
    rw [htape']
    have hne : q≠separator+11 := by omega
    by_cases hlt : q<stop
    · have hr : h+5≤q ∧ q<stop := ⟨hq,hlt⟩
      simp [clearAt,fillRange,hne,hr]
    · have he : q=stop := by omega
      subst q
      have hr : ¬ (h+5≤stop ∧ stop<stop) := by omega
      simp [clearAt,fillRange,setAt,hne,hr,show stop≠h+2 by omega,hmark]
  have hsep : touched separator=false := by
    rw [hframe' separator (le_refl _) (by omega)]
    exact hsepzero
  have hfive : Holds t (separator+1) (encode (List.replicate 5 0)) :=
    holds_prefix_word t (separator+1) _ (block 0 ++ tail) bank
  have hfive' : Holds touched (separator+1) (encode (List.replicate 5 0)) := by
    apply holds_transport t touched (separator+1) _ hfive
    intro q hq hq'
    have hq'' : q<separator+11 := by rw [hlen] at hq'; omega
    exact (hframe' q (by omega) (by omega)).symm
  have htarget : Holds touched (separator+11) [false,false] := by
    have hh := holds_prefix_word touched (separator+11) [false,false] tail (by simpa using hword')
    exact hh
  have hbank := holds_append_intro touched (separator+1) (encode (List.replicate 5 0))
    [false,false] hfive' (by simpa only [hpos] using htarget)
  let r := (separator-(h+6)).toNat
  let ys := unaryBankPrefix r (List.replicate 5 0)
  have hwindows := zero_windows h separator touched hlong hz1 hz2 hones hsep hbank
  change Prefix ys ∧ Prefix ys.reverse ∧
    downHolds touched (separator+9) (ys.reverse ++ [false,false]) ∧
    Holds touched (h+5) (ys ++ [false,false,false]) ∧
    separator+11=(h+2)+(ys.length : Int)+4 at hwindows
  obtain ⟨hys,hxs,hleft,hright,hposEq⟩ := hwindows
  have hlenRev : ys.reverse.length=ys.length := by simp
  have hposEq' : separator+11=(h+2)+(ys.reverse.length : Int)+4 := by simpa only [hlenRev] using hposEq
  have hleft' : downHolds touched (separator+11-2) (ys.reverse ++ [false,false]) := by
    have he : separator+11-2=separator+9 := by omega
    simpa only [he] using hleft
  have hz1' : touched (h+2+1)=false := by
    have he : h+2+1=h+3 := by omega
    simpa only [he] using hz1
  have hz2' : touched (h+2+2)=false := by
    have he : h+2+2=h+4 := by omega
    simpa only [he] using hz2
  have hright' : Holds touched (h+2+3) (ys ++ [false,false,false]) := by
    have he : h+2+3=h+5 := by omega
    simpa only [he] using hright
  obtain ⟨hrestored,hrestFrame,hsegment⟩ := restore_zero touched (h+2) (separator+11)
    ys.reverse ys hxs hys hlenRev hposEq' hleft' hmark' hz1' hz2' hright'
  let out := setAt (separator+11) (setAt (h+2+2) (clearAt (h+2) touched))
  have hsegment' : silentSegment machine (cfg 262 (separator+9) touched) (cfg 25 (separator+10) out)
      (2*ys.reverse.length+9) := by
    have he1 : separator+11-2=separator+9 := by omega
    have he2 : separator+11-1=separator+10 := by omega
    simpa only [he1,he2,out] using hsegment
  have ha' : physical.advance (cfg 99 h t) n=cfg 262 (separator+9) touched := by simpa only [hhead] using ha
  obtain ⟨ha'',hw''⟩ := append_silent _ _ _ n (2*ys.reverse.length+9) ha' hw hsegment'
  have hinit := holds_append_tail t (separator+1) (encode (List.replicate 5 0)) (block 0 ++ tail) bank
  have hinit' : Holds t (separator+11) (true :: false :: tail) := by
    simpa only [hpos,block_zero,List.cons_append,List.nil_append] using hinit
  have hposOriginal : t (separator+11)=true := hinit'.1
  have hbankFrame : ∀ q, separator≤q → out q=t q := by
    intro q hq
    by_cases he : q=separator+11
    · subst q
      simpa only [out,hposOriginal] using hrestored
    · have hh := hrestFrame q (by omega) he
      change out q=touched q at hh
      rw [hh]
      exact hframe' q hq he
  have hrestBank : Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) := by
    apply holds_transport t out _ _ bank
    intro q hq _
    exact (hbankFrame q (by omega)).symm
  have hmidFrame : ∀ q, q<h+2 → out q=mid q := by
    intro q hq
    have htouch : touched q=mid q := by
      rw [htape']
      have hn : ¬ (h+5≤q ∧ q<stop) := by omega
      simp [clearAt,fillRange,setAt,hn,show q≠separator+11 by omega,show q≠h+2 by omega]
    have hs : out q=touched q := by
      change setAt (separator+11) (setAt (h+2+2) (clearAt (h+2) touched)) q=touched q
      simp [setAt,clearAt,show q≠separator+11 by omega,show q≠h+2+2 by omega,
        show q≠h+2 by omega]
    rw [hs,htouch]
  have hcontrol6 : Holds out (h-4) [true,true,false,true,false,false] := by
    apply holds_transport mid out _ _ hmidWord
    intro q _ hq
    have hq' : q<h+2 := by simp at hq; omega
    exact (hmidFrame q hq').symm
  have hout2 : out (h+2)=false := by
    change setAt (separator+11) (setAt (h+2+2) (clearAt (h+2) touched)) (h+2)=false
    simp [setAt,clearAt,show h+2≠separator+11 by omega,show h+2≠h+2+2 by omega]
  have hout3 : out (h+3)=false := by
    change setAt (separator+11) (setAt (h+2+2) (clearAt (h+2) touched)) (h+3)=false
    simp [setAt,clearAt,show h+3≠separator+11 by omega,show h+3≠h+2+2 by omega,
      show h+3≠h+2 by omega,hz1]
  have hout4 : out (h+4)=true := by
    change setAt (separator+11) (setAt (h+2+2) (clearAt (h+2) touched)) (h+4)=true
    have he : h+4=h+2+2 := by omega
    simp [setAt,he,show h+4≠separator+11 by omega]
  have hcontrol3 : Holds out (h+2) [false,false,true] := by
    have he1 : h+2+1=h+3 := by omega
    have he2 : h+2+1+1=h+4 := by omega
    have he3 : h+3+1=h+4 := by omega
    simp only [Holds,he1,he2,he3,hout2,hout3,hout4,true_and]
  have hcontrol9 : Holds out (h-4) [true,true,false,true,false,false,false,false,true] := by
    have h := holds_append_intro out (h-4) [true,true,false,true,false,false]
      [false,false,true] hcontrol6 (by
        have he : h-4+(([true,true,false,true,false,false].length : Nat) : Int)=h+2 := by norm_num; omega
        rw [he]
        exact hcontrol3)
    exact h
  have hblank : ∀ q, q<h-4 → out q=false := by
    intro q hq
    rw [hmidFrame q (by omega)]
    exact hmidLeft q hq
  have hcontrol : ∀ q, h+4≤q → q<separator → out q=true := by
    intro q hq hq'
    by_cases he : q=h+4
    · simpa only [he] using hout4
    · have hf := hrestFrame q (by omega) (by omega)
      change out q=touched q at hf
      rw [hf]
      exact hones q (by omega) hq'
  exact ⟨n+(2*ys.reverse.length+9),out,by omega,hcontrol9,hblank,hcontrol,
    hbankFrame,hrestBank,ha'',hw''⟩

/-- The previously exported restored-bank contract remains available. -/
theorem supplied_beep_zero_restored (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+7≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false) (tail : List Bool)
    (bank : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail))) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) ∧
      physical.advance (cfg 99 h t) n=cfg 25 (separator+10) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,out,hn,_hw,_hl,_hc,hframe,hbank,ha,he⟩ :=
    supplied_beep_zero_restored_full h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hlong ones left hb right hsepzero tail bank
  exact ⟨n,out,hn,hframe,hbank,ha,he⟩

#print axioms supplied_beep_zero_restored_full
#print axioms supplied_beep_zero_restored
end Shared.Beeping.NPcoNP.NativeFirstZeroRestored
