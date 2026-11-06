import Shared.Beeping.NPcoNP.NativeFourthReturn25
import Shared.Beeping.NPcoNP.NativeSelectorParserGeneric
import Shared.Beeping.NPcoNP.NativeBeepZeroReturn

/-! The next carry and selector after the second zero-bank operation. All
reachability statements are conditional on an explicitly supplied layout. -/
namespace Shared.Beeping.NPcoNP.NativeFourthNextPath
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeBeepReturn
open Shared.Beeping.NPcoNP.NativeBeepZeroReturn
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeFirstNextPath
open Shared.Beeping.NPcoNP.NativeFourthReturn25
open Shared.Beeping.NPcoNP.NativeThirdNextPath
open Shared.Beeping.NPcoNP.NativeSelectorParserGeneric
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

def fifthPath : List Bool := [true,true,false,true,true,false,false,true,true,false,false]

theorem fifth_leaf : traceState557.acc.leaves[12]? =
    some (fifthPath,"3.$coalesced.10.decnz") := by decide

theorem fifth_retained : producerNumbering.map[12]?=some (some 8) := by decide

theorem fifth_path_walk : PreparedWalk fifthPath (.op "3.$coalesced.10.decnz") := by
  refine ⟨[true,true,false,false,true,true,false,false],rfl,?_⟩
  apply follow_sound producerGrammar [true,true,false,false,true,true,false,false] (.node producerGrammar.root)
  decide

theorem fifth_path_parse (t : Int → Bool) (h : Int) (hw : Holds t h fifthPath) :
    parseForward 52 t h=some ("3.$coalesced.10.decnz",11) := by
  apply (parseForward_iff t h "3.$coalesced.10.decnz" 11).2
  exact ⟨fifthPath,fifth_path_walk,rfl,hw⟩

theorem fifth_selector (h : Int) (t : Int → Bool)
    (word : Holds t (h-4) fifthPath) (left : ∀ q, q<h-4 → t q=false) :
    silentSegment machine (cfg 83 (h+3) t) (cfg 93 (h-3) t) 32 := by
  have hv := word
  simp only [fifthPath,Holds] at hv
  obtain ⟨hm4,hm3,hm2,hm1,h0,hp1,hp2,hp3,_⟩ := hv
  have hm3' : t (h-3)=true := by convert hm3 using 1 <;> congr 1 <;> omega
  have hm2' : t (h-2)=false := by convert hm2 using 1 <;> congr 1 <;> omega
  have hm1' : t (h-1)=true := by convert hm1 using 1 <;> congr 1 <;> omega
  have h0' : t h=true := by convert h0 using 1 <;> congr 1 <;> omega
  have hp1' : t (h+1)=false := by convert hp1 using 1 <;> congr 1 <;> omega
  have hp2' : t (h+2)=false := by convert hp2 using 1 <;> congr 1 <;> omega
  have hp3' : t (h+3)=true := by convert hp3 using 1 <;> congr 1 <;> omega
  let ks : List Nat := [1,0,2,2] ++ List.replicate 10 0
  have hw : downHolds t (h+3) (blocks ks ++ []) := by
    dsimp [ks,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | exact hp3' | (convert hp2' using 1 <;> congr 1 <;> omega) |
      (convert hp1' using 1 <;> congr 1 <;> omega) | (convert h0' using 1 <;> congr 1 <;> omega) |
      (convert hm1' using 1 <;> congr 1 <;> omega) | (convert hm2' using 1 <;> congr 1 <;> omega) |
      (convert hm3' using 1 <;> congr 1 <;> omega) | (convert hm4 using 1 <;> congr 1 <;> omega) |
      (apply left; omega)
  have hb := selector_to_parser t (h+3) (h-4) ks fifthPath
    "3.$coalesced.10.decnz" (by decide) hw (by simp [ks,blocks]; omega)
    left hm4 fifth_path_walk word
  have hd : (h-4-(h+3-19)).toNat=12 := by congr 1 <;> omega
  have he : h-4+1=h-3 := by omega
  simpa [ks,blocks,List.replicate_succ,fifthPath,hd,he] using hb.2.1

/-- A bounded carry from the supplied row-7 restoration reaches the full
row-8 selector boundary, preserving the whole bank suffix. -/
theorem carry_to_fifth_path (h b separator : Int) (t : Int → Bool)
    (hlong : h+11≤separator) (hw : Holds t (h-4) fourthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (h5 : t (h+5)=false) (h6 : t (h+6)=false) (h7 : t (h+7)=false)
    (control : ∀ q, h+8≤q → q<separator → t q=true)
    (hsep : t separator=false) (right : ∀ q, b≤q → t q=false) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧ Holds out (h-4) fifthPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.10.decnz",11) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+4<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 (h+4) t) (cfg 93 (h-3) out) n := by
  have hv := hw
  simp only [fourthPath,Holds] at hv
  obtain ⟨hm4,hm3,hm2,hm1,h0,hp1,hp2,hp3,hp4,_hp5,_⟩ := hv
  have hm4' : t (h-4)=true := hm4
  have hm3' : t (h-3)=true := by convert hm3 using 1 <;> congr 1 <;> omega
  have hm2' : t (h-2)=false := by convert hm2 using 1 <;> congr 1 <;> omega
  have hm1' : t (h-1)=true := by convert hm1 using 1 <;> congr 1 <;> omega
  have h0' : t h=true := by convert h0 using 1 <;> congr 1 <;> omega
  have hp1' : t (h+1)=false := by convert hp1 using 1 <;> congr 1 <;> omega
  have hp2' : t (h+2)=false := by convert hp2 using 1 <;> congr 1 <;> omega
  have hp3' : t (h+3)=true := by convert hp3 using 1 <;> congr 1 <;> omega
  have hp4' : t (h+4)=false := by convert hp4 using 1 <;> congr 1 <;> omega
  have hp8 : t (h+8)=true := control _ (by omega) (by omega)
  obtain ⟨n,out,hit,stop,hn,hmark,hframe,_hzero,hclear,hhit,hhitp,hhitstop,
      hhitOne,hstopOne,hstopZero,hones,hsuffix,hseg⟩ :=
    zero_carry_to83_detail_with_clear (h+4) (h+8) b t hp4' (by omega) hp8 right
  have hhitge : h+8≤hit := by
    by_contra hn'
    have he : hit=h+5 ∨ hit=h+6 ∨ hit=h+7 := by omega
    rcases he with he | he | he
    · rw [he,h5] at hhitOne; contradiction
    · rw [he,h6] at hhitOne; contradiction
    · rw [he,h7] at hhitOne; contradiction
  have hstopLt : stop<separator := by
    by_contra hn'
    have ho := hones separator (by omega) (by omega)
    rw [hsep] at ho
    contradiction
  have hstopEq : stop+1=separator := by
    by_contra hn'
    have ho := control (stop+1) (by omega) (by omega)
    rw [hstopZero] at ho
    contradiction
  have hleft : ∀ q, q<h-4 → out q=false := by
    intro q hq
    rw [hframe q (by omega)]
    exact left q hq
  have a4 : out (h-4)=true := by rw [hframe _ (by omega)]; exact hm4'
  have a3 : out (h-3)=true := by rw [hframe _ (by omega)]; exact hm3'
  have a2 : out (h-2)=false := by rw [hframe _ (by omega)]; exact hm2'
  have a1 : out (h-1)=true := by rw [hframe _ (by omega)]; exact hm1'
  have a0 : out h=true := by rw [hframe _ (by omega)]; exact h0'
  have b1 : out (h+1)=false := by rw [hframe _ (by omega)]; exact hp1'
  have b2 : out (h+2)=false := by rw [hframe _ (by omega)]; exact hp2'
  have b3 : out (h+3)=true := by rw [hframe _ (by omega)]; exact hp3'
  have hgap : ∀ q, h+4<q → q<separator-1 → out q=false := by
    intro q hq hq2
    exact hclear q hq (by omega)
  have hpath : Holds out (h-4) fifthPath := by
    dsimp [fifthPath,Holds]
    repeat' constructor
    all_goals first | exact a4 | (convert a3 using 1 <;> congr 1 <;> omega) |
      (convert a2 using 1 <;> congr 1 <;> omega) | (convert a1 using 1 <;> congr 1 <;> omega) |
      (convert a0 using 1 <;> congr 1 <;> omega) | (convert b1 using 1 <;> congr 1 <;> omega) |
      (convert b2 using 1 <;> congr 1 <;> omega) | (convert b3 using 1 <;> congr 1 <;> omega) |
      (convert hmark using 1 <;> congr 1 <;> omega) | (apply hgap <;> omega)
  have hselector := fifth_selector h out hpath hleft
  have hseg' : silentSegment machine (cfg 1 (h+4) t) (cfg 83 (h+3) out) n := by
    have he : h+4-1=h+3 := by omega
    simpa only [he] using hseg
  have hall := segAdd machine _ _ _ n 32 hseg' hselector
  refine ⟨n+32,out,by omega,hpath,fifth_path_parse out (h-4) hpath,hleft,hgap,?_,?_,?_⟩
  · have he : separator-1=stop := by omega
    rw [he,hsuffix stop (le_refl _)]
    exact hstopOne
  · intro q hq
    exact hsuffix q (by omega)
  · exact hall

/-- The literal table follows all ten remaining path bits in ten silent
steps. No tape cell changes; this identifies the physical entry state only. -/
theorem dispatch_fifth_path (h : Int) (t : Int → Bool) (hw : Holds t (h-4) fifthPath) :
    silentSegment machine (cfg 93 (h-3) t) (cfg 54 (h+7) t) 10 := by
  have hv := hw
  simp only [fifthPath,Holds] at hv
  obtain ⟨_h4,h3,h2,h1,h0,p1,p2,p3,p4,p5,p6,_⟩ := hv
  have h3' : t (h-3)=true := by convert h3 using 1 <;> congr 1 <;> omega
  have h2' : t (h-2)=false := by convert h2 using 1 <;> congr 1 <;> omega
  have h1' : t (h-1)=true := by convert h1 using 1 <;> congr 1 <;> omega
  have h0' : t h=true := by convert h0 using 1 <;> congr 1 <;> omega
  have p1' : t (h+1)=false := by convert p1 using 1 <;> congr 1 <;> omega
  have p2' : t (h+2)=false := by convert p2 using 1 <;> congr 1 <;> omega
  have p3' : t (h+3)=true := by convert p3 using 1 <;> congr 1 <;> omega
  have p4' : t (h+4)=true := by convert p4 using 1 <;> congr 1 <;> omega
  have p5' : t (h+5)=false := by convert p5 using 1 <;> congr 1 <;> omega
  have p6' : t (h+6)=false := by convert p6 using 1 <;> congr 1 <;> omega
  have a := dispatch_93_to166 h t h3' h2' h1'
  have b1 := oneSeg machine _ _ (unchanged_right 166 165 true h t (by decide) h0')
  have b2 := oneSeg machine _ _ (unchanged_right 165 164 false (h+1) t (by decide) p1')
  have b3 := oneSeg machine _ _ (unchanged_right 164 163 false (h+2) t (by decide) p2')
  have b4 := oneSeg machine _ _ (unchanged_right 163 162 true (h+3) t (by decide) p3')
  have b5 := oneSeg machine _ _ (unchanged_right 162 161 true (h+4) t (by decide) p4')
  have b6 := oneSeg machine _ _ (unchanged_right 161 248 false (h+5) t (by decide) p5')
  have b7 := oneSeg machine _ _ (unchanged_right 248 54 false (h+6) t (by decide) p6')
  have s1 := segAdd machine _ _ _ 3 1 a b1
  have s2 := segAdd machine _ _ _ 4 1 s1 b2
  have s2' : silentSegment machine (cfg 93 (h-3) t) (cfg 164 (h+2) t) 5 := by simpa [Int.add_assoc] using s2
  have s3 := segAdd machine _ _ _ 5 1 s2' b3
  have s3' : silentSegment machine (cfg 93 (h-3) t) (cfg 163 (h+3) t) 6 := by simpa [Int.add_assoc] using s3
  have s4 := segAdd machine _ _ _ 6 1 s3' b4
  have s4' : silentSegment machine (cfg 93 (h-3) t) (cfg 162 (h+4) t) 7 := by simpa [Int.add_assoc] using s4
  have s5 := segAdd machine _ _ _ 7 1 s4' b5
  have s5' : silentSegment machine (cfg 93 (h-3) t) (cfg 161 (h+5) t) 8 := by simpa [Int.add_assoc] using s5
  have s6 := segAdd machine _ _ _ 8 1 s5' b6
  have s6' : silentSegment machine (cfg 93 (h-3) t) (cfg 248 (h+6) t) 9 := by simpa [Int.add_assoc] using s6
  have all := segAdd machine _ _ _ 9 1 s6' b7
  simpa [Int.add_assoc] using all

/-- The supplied first-event layout reaches the next complete selector path,
with the original bank suffix and its single event preserved. -/
theorem supplied_beep_fifth_path (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+11≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false) (tail : List Bool)
    (bank : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail))) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧ Holds out (h-4) fifthPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.10.decnz",11) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+4<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) ∧
      physical.advance (cfg 99 h t) n=cfg 93 (h-3) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,mid,hn,hpath,hleft,h5,h6,h7,hcontrol,hframe,_hbank,ha,hw⟩ :=
    supplied_beep_fourth_return h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hlong ones left hb right hsepzero tail bank
  have hsep : mid separator=false := by rw [hframe separator (le_refl _)]; exact hsepzero
  let bound := max b separator
  have hright : ∀ q, bound≤q → mid q=false := by
    intro q hq
    rw [hframe q (le_trans (le_max_right _ _) hq)]
    exact right q (le_trans (le_max_left _ _) hq)
  obtain ⟨m,out,hm,hpath',hparse,hleft',hgap,hmarker,hframe',hcarry⟩ :=
    carry_to_fifth_path h bound separator mid hlong hpath hleft h5 h6 h7 hcontrol hsep hright
  obtain ⟨ha',hw'⟩ := append_silent _ _ _ n m ha hw hcarry
  have hfinal : ∀ q, separator≤q → out q=t q := by
    intro q hq
    rw [hframe' q hq]
    exact hframe q hq
  have hbank : Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) := by
    apply holds_transport t out _ _ bank
    intro q hq _
    exact (hfinal q (by omega)).symm
  exact ⟨n+m,out,by omega,hpath',hparse,hleft',hgap,hmarker,hfinal,hbank,ha',hw'⟩

/-- The supplied first-event layout reaches literal state 54 for
retained row 8, preserving its full prepared path, bank suffix and single beep. -/
theorem supplied_beep_fifth_dispatch (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+11≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false) (tail : List Bool)
    (bank : Holds t (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail))) :
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧ Holds out (h-4) fifthPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.10.decnz",11) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+4<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (encode (List.replicate 5 0) ++ (block 0 ++ tail)) ∧
      physical.advance (cfg 99 h t) n=cfg 54 (h+7) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  obtain ⟨n,out,hn,hpath,hparse,hleft,hgap,hmark,hframe,hbank,ha,hw⟩ :=
    supplied_beep_fifth_path h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hlong ones left hb right hsepzero tail bank
  have hdispatch := dispatch_fifth_path h out hpath
  obtain ⟨ha',hw'⟩ := append_silent _ _ _ n 10 ha hw hdispatch
  exact ⟨n+10,out,by omega,hpath,hparse,hleft,hgap,hmark,hframe,hbank,ha',hw'⟩

#print axioms dispatch_fifth_path
#print axioms supplied_beep_fifth_dispatch
#print axioms supplied_beep_fifth_path
#print axioms fifth_retained
#print axioms fifth_leaf
#print axioms fifth_selector
#print axioms carry_to_fifth_path
end Shared.Beeping.NPcoNP.NativeFourthNextPath
