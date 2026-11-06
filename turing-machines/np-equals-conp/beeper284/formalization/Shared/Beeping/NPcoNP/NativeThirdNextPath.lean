import Shared.Beeping.NPcoNP.NativeThirdReturn25
import Shared.Beeping.NPcoNP.NativeBeepZeroReturn

/-! The set-cell carry and selector following the first-bank restoration. -/
namespace Shared.Beeping.NPcoNP.NativeThirdNextPath
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeBeepZeroReturn
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeFirstNextPath
open Shared.Beeping.NPcoNP.NativeSecondNextPath
open Shared.Beeping.NPcoNP.NativeThirdReturn25
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.GrammarFullRowsCoverage
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def fourthPath : List Bool := [true,true,false,true,true,false,false,true,false,false]

theorem fourth_leaf : traceState557.acc.leaves[10]? =
    some (fourthPath,"3.$coalesced.0.decnz") := by decide

theorem fourth_retained : producerNumbering.map[10]?=some (some 7) := by decide

theorem fourth_path_walk : PreparedWalk fourthPath (.op "3.$coalesced.0.decnz") := by
  refine ⟨[true,true,false,false,true,false,false],rfl,?_⟩
  apply follow_sound producerGrammar [true,true,false,false,true,false,false] (.node producerGrammar.root)
  decide

theorem fourth_path_parse (t : Int → Bool) (h : Int) (hw : Holds t h fourthPath) :
    parseForward 52 t h=some ("3.$coalesced.0.decnz",10) := by
  apply (parseForward_iff t h "3.$coalesced.0.decnz" 10).2
  exact ⟨fourthPath,fourth_path_walk,rfl,hw⟩

theorem fourth_selector (h : Int) (t : Int → Bool)
    (hm4 : t (h-4)=true) (hm3 : t (h-3)=true) (hm2 : t (h-2)=false)
    (hm1 : t (h-1)=true) (h0 : t h=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (left : ∀ q, q<h-4 → t q=false) :
    silentSegment machine (cfg 83 (h+2) t) (cfg 93 (h-3) t) 31 := by
  let ks : List Nat := [0,0,2,2] ++ List.replicate 10 0
  have hw : downHolds t (h+2) (blocks ks ++ []) := by
    dsimp [ks,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | exact hp2 | (convert hp1 using 1 <;> congr 1 <;> omega) |
      (convert h0 using 1 <;> congr 1 <;> omega) | (convert hm1 using 1 <;> congr 1 <;> omega) |
      (convert hm2 using 1 <;> congr 1 <;> omega) | (convert hm3 using 1 <;> congr 1 <;> omega) |
      (convert hm4 using 1 <;> congr 1 <;> omega) | (apply left; omega)
  have hs := (chain_blocks chain83 ks (h+2) t [] (by decide) hw).2
  have hs' : silentSegment machine (cfg 83 (h+2) t) (cfg 92 (h-16) t) 18 := by
    have he : h+2-18=h-16 := by omega
    simpa [ks,blocks,List.replicate_succ,he] using hs
  have hz : ∀ i : Nat, i<12 → t ((h-16)+(i : Int))=false := by
    intro i hi
    apply left
    omega
  have ho : t ((h-16)+(12 : Int))=true := by
    have he : h-16+12=h-4 := by omega
    simpa only [he] using hm4
  have hr := scan92_exact 12 (h-16) t hz ho
  have hall := segAdd machine _ _ _ 18 13 hs' hr
  convert hall using 1 <;> congr 1 <;> omega

/-- The set-cell carry is a paid silent first step, followed by a bounded
zero-cell carry and the selector. -/
theorem carry_to_fourth_path (h b separator : Int) (t : Int → Bool)
    (hlong : h+11≤separator) (hw : Holds t (h-4) thirdPath)
    (left : ∀ q, q<h-4 → t q=false)
    (h5 : t (h+5)=false) (h6 : t (h+6)=false) (h7 : t (h+7)=false)
    (control : ∀ q, h+8≤q → q<separator → t q=true)
    (hsep : t separator=false) (right : ∀ q, b≤q → t q=false) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧ Holds out (h-4) fourthPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.0.decnz",10) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+3<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 (h+4) t) (cfg 93 (h-3) out) n := by
  have hv := hw
  simp only [thirdPath,Holds] at hv
  obtain ⟨hm4,hm3,hm2,hm1,h0,hp1,hp2,hp3,hp4,_hp5,_⟩ := hv
  have hm4' : t (h-4)=true := hm4
  have hm3' : t (h-3)=true := by convert hm3 using 1 <;> congr 1 <;> omega
  have hm2' : t (h-2)=false := by convert hm2 using 1 <;> congr 1 <;> omega
  have hm1' : t (h-1)=true := by convert hm1 using 1 <;> congr 1 <;> omega
  have h0' : t h=true := by convert h0 using 1 <;> congr 1 <;> omega
  have hp1' : t (h+1)=false := by convert hp1 using 1 <;> congr 1 <;> omega
  have hp2' : t (h+2)=false := by convert hp2 using 1 <;> congr 1 <;> omega
  have hp3' : t (h+3)=false := by convert hp3 using 1 <;> congr 1 <;> omega
  have hp4' : t (h+4)=true := by convert hp4 using 1 <;> congr 1 <;> omega
  let u := put t (h+4) false
  have huz : u (h+3)=false := by simp [u,put,show h+3≠h+4 by omega,hp3']
  have hu4 : u (h+4)=false := by simp [u,put]
  have hu5 : u (h+5)=false := by simp [u,put,show h+5≠h+4 by omega,h5]
  have hu6 : u (h+6)=false := by simp [u,put,show h+6≠h+4 by omega,h6]
  have hu7 : u (h+7)=false := by simp [u,put,show h+7≠h+4 by omega,h7]
  have hucontrol : ∀ q, h+8≤q → q<separator → u q=true := by
    intro q hq hq2
    simp [u,put,show q≠h+4 by omega,control q hq hq2]
  have husep : u separator=false := by simp [u,put,show separator≠h+4 by omega,hsep]
  have huright : ∀ q, b≤q → u q=false := by
    intro q hq
    by_cases he : q=h+4
    · simp [u,put,he]
    · simp [u,put,he,right q hq]
  have hup8 : u (h+8)=true := hucontrol _ (by omega) (by omega)
  obtain ⟨n,out,hit,stop,hn,hmark,hframe,_hzero,hclear,hhit,hhitp,hhitstop,
      hhitOne,hstopOne,hstopZero,hones,hsuffix,hseg⟩ :=
    zero_carry_to83_detail_with_clear (h+3) (h+8) b u huz (by omega) hup8 huright
  have hhitge : h+8≤hit := by
    by_contra hn'
    have he : hit=h+4 ∨ hit=h+5 ∨ hit=h+6 ∨ hit=h+7 := by omega
    rcases he with he | he | he | he
    · rw [he,hu4] at hhitOne; contradiction
    · rw [he,hu5] at hhitOne; contradiction
    · rw [he,hu6] at hhitOne; contradiction
    · rw [he,hu7] at hhitOne; contradiction
  have hstopLt : stop<separator := by
    by_contra hn'
    have ho := hones separator (by omega) (by omega)
    rw [husep] at ho
    contradiction
  have hstopEq : stop+1=separator := by
    by_contra hn'
    have ho := hucontrol (stop+1) (by omega) (by omega)
    rw [hstopZero] at ho
    contradiction
  have hprefix : ∀ q, q<h+3 → out q=t q := by
    intro q hq
    rw [hframe q hq]
    simp [u,put,show q≠h+4 by omega]
  have hleft : ∀ q, q<h-4 → out q=false := by
    intro q hq
    rw [hprefix q (by omega)]
    exact left q hq
  have a4 : out (h-4)=true := by rw [hprefix _ (by omega)]; exact hm4'
  have a3 : out (h-3)=true := by rw [hprefix _ (by omega)]; exact hm3'
  have a2 : out (h-2)=false := by rw [hprefix _ (by omega)]; exact hm2'
  have a1 : out (h-1)=true := by rw [hprefix _ (by omega)]; exact hm1'
  have a0 : out h=true := by rw [hprefix _ (by omega)]; exact h0'
  have b1 : out (h+1)=false := by rw [hprefix _ (by omega)]; exact hp1'
  have b2 : out (h+2)=false := by rw [hprefix _ (by omega)]; exact hp2'
  have hgap : ∀ q, h+3<q → q<separator-1 → out q=false := by
    intro q hq hq2
    exact hclear q hq (by omega)
  have hpath : Holds out (h-4) fourthPath := by
    dsimp [fourthPath,Holds]
    repeat' constructor
    all_goals first | exact a4 | (convert a3 using 1 <;> congr 1 <;> omega) |
      (convert a2 using 1 <;> congr 1 <;> omega) | (convert a1 using 1 <;> congr 1 <;> omega) |
      (convert a0 using 1 <;> congr 1 <;> omega) | (convert b1 using 1 <;> congr 1 <;> omega) |
      (convert b2 using 1 <;> congr 1 <;> omega) | (convert hmark using 1 <;> congr 1 <;> omega) |
      (apply hgap <;> omega)
  have hselector := fourth_selector h out a4 a3 a2 a1 a0 b1 b2 hleft
  have hseg' : silentSegment machine (cfg 1 (h+3) u) (cfg 83 (h+2) out) n := by
    have he : h+3-1=h+2 := by omega
    simpa only [he] using hseg
  have hfirst : silentSegment machine (cfg 1 (h+4) t) (cfg 1 (h+3) u) 1 := by
    have he : h+4-1=h+3 := by omega
    simpa only [he,u] using oneSeg machine _ _ (NativeHalfState1Scan.step_one (h+4) t hp4')
  have hmid := segAdd machine _ _ _ 1 n hfirst hseg'
  have hall := segAdd machine _ _ _ (1+n) 31 hmid hselector
  refine ⟨1+n+31,out,by omega,hpath,fourth_path_parse out (h-4) hpath,hleft,hgap,?_,?_,hall⟩
  · have he : separator-1=stop := by omega
    rw [he,hsuffix stop (le_refl _)]
    exact hstopOne
  · intro q hq
    rw [hsuffix q (by omega)]
    simp [u,put,show q≠h+4 by omega]

/-- Paid silent dispatcher for the checked row-7 path. -/
theorem dispatch_fourth_path (h : Int) (t : Int → Bool) (hw : Holds t (h-4) fourthPath) :
    silentSegment machine (cfg 93 (h-3) t) (cfg 50 (h+6) t) 9 := by
  have hv := hw
  simp only [fourthPath,Holds] at hv
  obtain ⟨_h4,h3,h2,h1,h0,p1,p2,p3,p4,p5,_⟩ := hv
  have h3' : t (h-3)=true := by convert h3 using 1 <;> congr 1 <;> omega
  have h2' : t (h-2)=false := by convert h2 using 1 <;> congr 1 <;> omega
  have h1' : t (h-1)=true := by convert h1 using 1 <;> congr 1 <;> omega
  have h0' : t h=true := by convert h0 using 1 <;> congr 1 <;> omega
  have p1' : t (h+1)=false := by convert p1 using 1 <;> congr 1 <;> omega
  have p2' : t (h+2)=false := by convert p2 using 1 <;> congr 1 <;> omega
  have p3' : t (h+3)=true := by convert p3 using 1 <;> congr 1 <;> omega
  have p4' : t (h+4)=false := by convert p4 using 1 <;> congr 1 <;> omega
  have p5' : t (h+5)=false := by convert p5 using 1 <;> congr 1 <;> omega
  have a := dispatch_93_to166 h t h3' h2' h1'
  have b1 := oneSeg machine _ _ (unchanged_right 166 165 true h t (by decide) h0')
  have b2 := oneSeg machine _ _ (unchanged_right 165 164 false (h+1) t (by decide) p1')
  have b3 := oneSeg machine _ _ (unchanged_right 164 163 false (h+2) t (by decide) p2')
  have b4 := oneSeg machine _ _ (unchanged_right 163 162 true (h+3) t (by decide) p3')
  have b5 := oneSeg machine _ _ (unchanged_right 162 226 false (h+4) t (by decide) p4')
  have b6 := oneSeg machine _ _ (unchanged_right 226 50 false (h+5) t (by decide) p5')
  have s1 := segAdd machine _ _ _ 3 1 a b1
  have s2 := segAdd machine _ _ _ 4 1 s1 b2
  have s2' : silentSegment machine (cfg 93 (h-3) t) (cfg 164 (h+2) t) 5 := by simpa [Int.add_assoc] using s2
  have s3 := segAdd machine _ _ _ 5 1 s2' b3
  have s3' : silentSegment machine (cfg 93 (h-3) t) (cfg 163 (h+3) t) 6 := by simpa [Int.add_assoc] using s3
  have s4 := segAdd machine _ _ _ 6 1 s3' b4
  have s4' : silentSegment machine (cfg 93 (h-3) t) (cfg 162 (h+4) t) 7 := by simpa [Int.add_assoc] using s4
  have s5 := segAdd machine _ _ _ 7 1 s4' b5
  have s5' : silentSegment machine (cfg 93 (h-3) t) (cfg 226 (h+5) t) 8 := by simpa [Int.add_assoc] using s5
  have all := segAdd machine _ _ _ 8 1 s5' b6
  simpa [Int.add_assoc] using all

/-- The supplied first-event layout reaches the checked row-7 literal
dispatch, with its entire bank suffix and exactly one beep. -/
theorem supplied_beep_fourth_dispatch (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+11≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false) (tail : List Bool)
    (bank : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail))) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧ Holds out (h-4) fourthPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.0.decnz",10) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+3<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) ∧
      physical.advance (cfg 99 h t) n=cfg 50 (h+6) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,mid,hn,hpath,hleft,h5,h6,h7,hcontrol,hframe,_hbank,ha,hw⟩ :=
    supplied_beep_third_return h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hlong ones left hb right hsepzero tail bank
  have hsep : mid separator=false := by rw [hframe separator (le_refl _)]; exact hsepzero
  let bound := max b separator
  have hright : ∀ q, bound≤q → mid q=false := by
    intro q hq
    rw [hframe q (le_trans (le_max_right _ _) hq)]
    exact right q (le_trans (le_max_left _ _) hq)
  obtain ⟨m,out,hm,hpath',hparse,hleft',hgap,hmarker,hframe',hcarry⟩ :=
    carry_to_fourth_path h bound separator mid hlong hpath hleft h5 h6 h7 hcontrol hsep hright
  obtain ⟨ha',hw'⟩ := append_silent _ _ _ n m ha hw hcarry
  have hfinal : ∀ q, separator≤q → out q=t q := by
    intro q hq
    rw [hframe' q hq]
    exact hframe q hq
  have hbank : Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) := by
    apply holds_transport t out _ _ bank
    intro q hq _
    exact (hfinal q (by omega)).symm
  have hdispatch := dispatch_fourth_path h out hpath'
  obtain ⟨ha'',hw''⟩ := append_silent _ _ _ (n+m) 9 ha' hw' hdispatch
  exact ⟨n+m+9,out,by omega,hpath',hparse,hleft',hgap,hmarker,hfinal,hbank,ha'',hw''⟩

#print axioms dispatch_fourth_path
#print axioms supplied_beep_fourth_dispatch
#print axioms fourth_leaf
#print axioms fourth_retained
#print axioms carry_to_fourth_path
end Shared.Beeping.NPcoNP.NativeThirdNextPath
