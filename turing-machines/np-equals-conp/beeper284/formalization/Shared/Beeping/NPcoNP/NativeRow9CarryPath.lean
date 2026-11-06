import Shared.Beeping.NPcoNP.NativeFifthCarryPath

/-! Conditional progress through the continuation after the row-9 increment. -/
namespace Shared.Beeping.NPcoNP.NativeRow9CarryPath
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeBeepZeroReturn
open Shared.Beeping.NPcoNP.NativeFifthNextPath
open Shared.Beeping.NPcoNP.NativeSelectorParserGeneric
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def continuationPath : List Bool := [true,true,false,true,true,false,false,true,true,false,true,true]

theorem continuation_path_walk : PreparedWalk continuationPath (.op "_continue.2") := by
  refine ⟨[true,true,false,false,true,true,false,true,true],rfl,?_⟩
  apply follow_sound producerGrammar [true,true,false,false,true,true,false,true,true] (.node producerGrammar.root)
  decide

theorem continuation_path_parse (t : Int → Bool) (h : Int) (hw : Holds t h continuationPath) :
    parseForward 52 t h=some ("_continue.2",12) := by
  apply (parseForward_iff t h "_continue.2" 12).2
  exact ⟨continuationPath,continuation_path_walk,rfl,hw⟩

theorem continuation_selector (h : Int) (t : Int → Bool)
    (word : Holds t (h-4) continuationPath) (left : ∀ q, q<h-4 → t q=false) :
    silentSegment machine (cfg 83 (h+6) t) (cfg 93 (h-3) t) 33 := by
  have hv := word
  simp only [continuationPath,Holds] at hv
  obtain ⟨hm4,hm3,hm2,hm1,h0,hp1,hp2,hp3,hp4,hp5,hp6,_⟩ := hv
  have hm3' : t (h-3)=true := by convert hm3 using 1 <;> congr 1 <;> omega
  have hm2' : t (h-2)=false := by convert hm2 using 1 <;> congr 1 <;> omega
  have hm1' : t (h-1)=true := by convert hm1 using 1 <;> congr 1 <;> omega
  have h0' : t h=true := by convert h0 using 1 <;> congr 1 <;> omega
  have hp1' : t (h+1)=false := by convert hp1 using 1 <;> congr 1 <;> omega
  have hp2' : t (h+2)=false := by convert hp2 using 1 <;> congr 1 <;> omega
  have hp3' : t (h+3)=true := by convert hp3 using 1 <;> congr 1 <;> omega
  have hp4' : t (h+4)=true := by convert hp4 using 1 <;> congr 1 <;> omega
  have hp5' : t (h+5)=false := by convert hp5 using 1 <;> congr 1 <;> omega
  have hp6' : t (h+6)=true := by convert hp6 using 1 <;> congr 1 <;> omega
  let ks : List Nat := [1,2,0,2,2] ++ List.replicate 9 0
  have hw : downHolds t (h+6) (blocks ks ++ []) := by
    dsimp [ks,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | exact hp6' | (convert hp5' using 1 <;> congr 1 <;> omega) | (convert hp4' using 1 <;> congr 1 <;> omega) |
      (convert hp3' using 1 <;> congr 1 <;> omega) | (convert hp2' using 1 <;> congr 1 <;> omega) |
      (convert hp1' using 1 <;> congr 1 <;> omega) | (convert h0' using 1 <;> congr 1 <;> omega) |
      (convert hm1' using 1 <;> congr 1 <;> omega) | (convert hm2' using 1 <;> congr 1 <;> omega) |
      (convert hm3' using 1 <;> congr 1 <;> omega) | (convert hm4 using 1 <;> congr 1 <;> omega) |
      (apply left; omega)
  have hb := selector_to_parser t (h+6) (h-4) ks continuationPath
    "_continue.2" (by decide) hw (by simp [ks,blocks]; omega)
    left hm4 continuation_path_walk word
  have hd : (h-4-(h+6-21)).toNat=11 := by congr 1 <;> omega
  have he : h-4+1=h-3 := by omega
  simpa [ks,blocks,List.replicate_succ,continuationPath,hd,he] using hb.2.1

theorem carry_to_continuation_path (h b separator : Int) (t : Int → Bool)
    (hlong : h+12≤separator) (hw : Holds t (h-4) sixthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (h8 : t (h+8)=false) (h9 : t (h+9)=false)
    (control : ∀ q, h+10≤q → q<separator → t q=true)
    (hsep : t separator=false) (right : ∀ q, b≤q → t q=false) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧ Holds out (h-4) continuationPath ∧
      parseForward 52 out (h-4)=some ("_continue.2",12) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+7<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 (h+7) t) (cfg 93 (h-3) out) n := by
  have hv := hw
  simp only [sixthPath,Holds] at hv
  obtain ⟨hm4,hm3,hm2,hm1,h0,hp1,hp2,hp3,hp4,hp5,hp6,hp7,_⟩ := hv
  have hm4' : t (h-4)=true := hm4
  have hm3' : t (h-3)=true := by convert hm3 using 1 <;> congr 1 <;> omega
  have hm2' : t (h-2)=false := by convert hm2 using 1 <;> congr 1 <;> omega
  have hm1' : t (h-1)=true := by convert hm1 using 1 <;> congr 1 <;> omega
  have h0' : t h=true := by convert h0 using 1 <;> congr 1 <;> omega
  have hp1' : t (h+1)=false := by convert hp1 using 1 <;> congr 1 <;> omega
  have hp2' : t (h+2)=false := by convert hp2 using 1 <;> congr 1 <;> omega
  have hp3' : t (h+3)=true := by convert hp3 using 1 <;> congr 1 <;> omega
  have hp4' : t (h+4)=true := by convert hp4 using 1 <;> congr 1 <;> omega
  have hp5' : t (h+5)=false := by convert hp5 using 1 <;> congr 1 <;> omega
  have hp6' : t (h+6)=true := by convert hp6 using 1 <;> congr 1 <;> omega
  have hp7' : t (h+7)=false := by convert hp7 using 1 <;> congr 1 <;> omega
  have hp10 : t (h+10)=true := control _ (by omega) (by omega)
  obtain ⟨n,out,hit,stop,hn,hmark,hframe,_hzero,hclear,hhit,hhitp,hhitstop,
      hhitOne,hstopOne,hstopZero,hones,hsuffix,hseg⟩ :=
    zero_carry_to83_detail_with_clear (h+7) (h+10) b t hp7' (by omega) hp10 right
  have hhitge : h+10≤hit := by
    by_contra hn'
    have he : hit=h+8 ∨ hit=h+9 := by omega
    rcases he with he | he
    · rw [he,h8] at hhitOne; contradiction
    · rw [he,h9] at hhitOne; contradiction
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
  have b4 : out (h+4)=true := by rw [hframe _ (by omega)]; exact hp4'
  have b5 : out (h+5)=false := by rw [hframe _ (by omega)]; exact hp5'
  have b6 : out (h+6)=true := by rw [hframe _ (by omega)]; exact hp6'
  have hgap : ∀ q, h+7<q → q<separator-1 → out q=false := by
    intro q hq hq2
    exact hclear q hq (by omega)
  have hpath : Holds out (h-4) continuationPath := by
    dsimp [continuationPath,Holds]
    repeat' constructor
    all_goals first | exact a4 | (convert a3 using 1 <;> congr 1 <;> omega) |
      (convert a2 using 1 <;> congr 1 <;> omega) | (convert a1 using 1 <;> congr 1 <;> omega) |
      (convert a0 using 1 <;> congr 1 <;> omega) | (convert b1 using 1 <;> congr 1 <;> omega) |
      (convert b2 using 1 <;> congr 1 <;> omega) | (convert b3 using 1 <;> congr 1 <;> omega) |
      (convert b4 using 1 <;> congr 1 <;> omega) | (convert b5 using 1 <;> congr 1 <;> omega) |
      (convert b6 using 1 <;> congr 1 <;> omega) | (convert hmark using 1 <;> congr 1 <;> omega) | (apply hgap <;> omega)
  have hselector := continuation_selector h out hpath hleft
  have hseg' : silentSegment machine (cfg 1 (h+7) t) (cfg 83 (h+6) out) n := by
    have he : h+7-1=h+6 := by omega
    simpa only [he] using hseg
  have hall := segAdd machine _ _ _ n 33 hseg' hselector
  refine ⟨n+33,out,by omega,hpath,continuation_path_parse out (h-4) hpath,hleft,hgap,?_,?_,?_⟩
  · have he : separator-1=stop := by omega
    rw [he,hsuffix stop (le_refl _)]
    exact hstopOne
  · intro q hq
    exact hsuffix q (by omega)
  · exact hall

#print axioms carry_to_continuation_path
end Shared.Beeping.NPcoNP.NativeRow9CarryPath
