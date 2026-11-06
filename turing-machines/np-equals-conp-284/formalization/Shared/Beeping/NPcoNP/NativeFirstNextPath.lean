import Shared.Beeping.NPcoNP.NativeFirstReturn25
import Shared.Beeping.NPcoNP.NativeBeepForwardGraph

/-! The zero-branch carry produces the next full prepared path. The path is
checked against the retained producer graph; general compiler correctness and
blank-start reachability are separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeFirstNextPath
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeBeepZeroReturn
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.GrammarFullRowsCoverage
open Shared.Beeping.NPcoNP.Parent290Coalesced
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

def nextPath : List Bool := [true,true,false,true,true,false,false,false,false,false]

theorem next_leaf : traceState557.acc.leaves[3]? =
    some (nextPath,"3.$coalesced.4.decnz") := by decide

theorem next_retained : producerNumbering.map[3]?=some (some 2) := by decide

theorem next_graph_instruction :
    let ins := target.code[2]
    ins.action=.base (.decNZ 4) ∧ ins.yes=3 ∧ ins.no=5 := by
  exact ⟨rfl,rfl,rfl⟩

theorem next_path_walk : PreparedWalk nextPath (.op "3.$coalesced.4.decnz") := by
  refine ⟨[true,true,false,false,false,false,false],rfl,?_⟩
  apply follow_sound producerGrammar [true,true,false,false,false,false,false] (.node producerGrammar.root)
  decide

theorem next_path_parse (t : Int → Bool) (h : Int) (hw : Holds t h nextPath) :
    parseForward 52 t h=some ("3.$coalesced.4.decnz",10) := by
  apply (parseForward_iff t h "3.$coalesced.4.decnz" 10).2
  exact ⟨nextPath,next_path_walk,rfl,hw⟩

/-- The next 14-state selector scan has fixed duration and leaves the tape
unchanged when its left-hand control bits and blank tail are supplied. -/
theorem next_selector (h : Int) (t : Int → Bool)
    (h1 : t (h-1)=true) (h2 : t (h-2)=false)
    (h3 : t (h-3)=true) (h4 : t (h-4)=true)
    (left : ∀ q, q<h-4 → t q=false) :
    silentSegment machine (cfg 83 (h-1) t) (cfg 93 (h-3) t) 32 := by
  let ks : List Nat := [1,2] ++ List.replicate 12 0
  have hw : downHolds t (h-1) (blocks ks ++ []) := by
    dsimp [ks,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | exact h1 | (convert h2 using 1 <;> congr 1 <;> omega) |
      (convert h3 using 1 <;> congr 1 <;> omega) |
      (convert h4 using 1 <;> congr 1 <;> omega) | (apply left; omega)
  have hs := (chain_blocks chain83 ks (h-1) t [] (by decide) hw).2
  have hs' : silentSegment machine (cfg 83 (h-1) t) (cfg 92 (h-18) t) 17 := by
    have he : h-1-17=h-18 := by omega
    simpa [ks,blocks,List.replicate_succ,he] using hs
  have hz : ∀ i : Nat, i<14 → t ((h-18)+(i : Int))=false := by
    intro i hi
    apply left
    omega
  have ho : t ((h-18)+(14 : Int))=true := by
    have he : h-18+14=h-4 := by omega
    simpa only [he] using h4
  have hr := scan92_exact 14 (h-18) t hz ho
  have hall := segAdd machine _ _ _ 17 15 hs' hr
  convert hall using 1 <;> congr 1 <;> omega

/-- The carry beginning at state 1, followed by the complete selector, reaches
state 93 with the next full grammar path and preserves the bank suffix. -/
theorem carry_to_next_path_full (h b separator : Int) (t : Int → Bool)
    (hlong : h+7≤separator)
    (hw : Holds t (h-4) [true,true,false,true,false,false,false,false,true])
    (left : ∀ q, q<h-4 → t q=false)
    (control : ∀ q, h+4≤q → q<separator → t q=true)
    (hsepzero : t separator=false)
    (right : ∀ q, b≤q → t q=false) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      Holds out (h-4) nextPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.4.decnz",10) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 93 (h-3) out) n := by
  have hv := hw
  simp only [Holds] at hv
  obtain ⟨hm4,hm3,hm2,hm1,h0,hp1,hp2,hp3,hp4,_⟩ := hv
  have hm4' : t (h-4)=true := hm4
  have hm3' : t (h-3)=true := by convert hm3 using 1 <;> congr 1 <;> omega
  have hm2' : t (h-2)=false := by convert hm2 using 1 <;> congr 1 <;> omega
  have hm1' : t (h-1)=true := by convert hm1 using 1 <;> congr 1 <;> omega
  have h0' : t h=false := by convert h0 using 1 <;> congr 1 <;> omega
  have hp1' : t (h+1)=false := by convert hp1 using 1 <;> congr 1 <;> omega
  have hp2' : t (h+2)=false := by convert hp2 using 1 <;> congr 1 <;> omega
  have hp3' : t (h+3)=false := by convert hp3 using 1 <;> congr 1 <;> omega
  have hp4' : t (h+4)=true := by convert hp4 using 1 <;> congr 1 <;> omega
  obtain ⟨n,out,hit,stop,hn,hmark,hframe,_hzero,hclear,hhit,hhitp,hhitstop,
      hhitOne,hstopOne,hstopZero,hones,hsuffix,hseg⟩ :=
    zero_carry_to83_detail_with_clear h (h+4) b t h0' (by omega) hp4' right
  have hhitge : h+4≤hit := by
    by_contra hn'
    have he : hit=h+1 ∨ hit=h+2 ∨ hit=h+3 := by omega
    rcases he with he | he | he
    · rw [he,hp1'] at hhitOne; contradiction
    · rw [he,hp2'] at hhitOne; contradiction
    · rw [he,hp3'] at hhitOne; contradiction
  have hstopLt : stop<separator := by
    by_contra hn'
    have ho := hones separator (by omega) (by omega)
    rw [hsepzero] at ho
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
  have h4 : out (h-4)=true := by rw [hframe _ (by omega)]; exact hm4'
  have h3 : out (h-3)=true := by rw [hframe _ (by omega)]; exact hm3'
  have h2 : out (h-2)=false := by rw [hframe _ (by omega)]; exact hm2'
  have h1 : out (h-1)=true := by rw [hframe _ (by omega)]; exact hm1'
  have hz : ∀ q, h<q → q≤h+5 → out q=false := by
    intro q hq hq'
    exact hclear q hq (by omega)
  have hpath : Holds out (h-4) nextPath := by
    dsimp [nextPath,Holds]
    repeat' constructor
    all_goals first | exact h4 | (convert h3 using 1 <;> congr 1 <;> omega) |
      (convert h2 using 1 <;> congr 1 <;> omega) |
      (convert h1 using 1 <;> congr 1 <;> omega) |
      (convert hmark using 1 <;> congr 1 <;> omega) | (apply hz <;> omega)
  have hselector := next_selector h out h1 h2 h3 h4 hleft
  have hall := segAdd machine _ _ _ n 32 hseg hselector
  refine ⟨n+32,out,by omega,hpath,next_path_parse out (h-4) hpath,hleft,?_,?_,?_,hall⟩
  · intro q hq hq2
    exact hclear q hq (by omega)
  · have he : separator-1=stop := by omega
    rw [he, hsuffix stop (le_refl _)]
    exact hstopOne
  · intro q hq
    exact hsuffix q (by omega)

/-- Compatibility projection of the strengthened carry invariant. -/
theorem carry_to_next_path (h b separator : Int) (t : Int → Bool)
    (hlong : h+7≤separator)
    (hw : Holds t (h-4) [true,true,false,true,false,false,false,false,true])
    (left : ∀ q, q<h-4 → t q=false)
    (control : ∀ q, h+4≤q → q<separator → t q=true)
    (hsepzero : t separator=false)
    (right : ∀ q, b≤q → t q=false) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      Holds out (h-4) nextPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.4.decnz",10) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 93 (h-3) out) n := by
  obtain ⟨n,out,hn,hp,hparse,hl,_,_,hr,hs⟩ :=
    carry_to_next_path_full h b separator t hlong hw left control hsepzero right
  exact ⟨n,out,hn,hp,hparse,hl,hr,hs⟩

theorem unchanged_right (q r : Fin 284) (v : Bool) (h : Int) (t : Int → Bool)
    (row : machine.table.row q v=⟨v,.right,r,false⟩) (hv : t h=v) :
    machine.step (cfg q h t)=(cfg r (h+1) t,false) := by
  have hw : (⟨q,h,t⟩ : Config 284).write v=t := by rw [←hv]; exact NativeHalfRows.write_current _
  simp [cfg,Machine.step,hv,row,Move.apply,hw]

/-- The literal dispatcher follows the nine bits after the header in nine paid
silent steps from state 93 to state 62. The whole tape remains unchanged. -/
theorem dispatch_next_path (h : Int) (t : Int → Bool) (hw : Holds t (h-4) nextPath) :
    silentSegment machine (cfg 93 (h-3) t) (cfg 62 (h+6) t) 9 := by
  have hv := hw
  simp only [nextPath,Holds] at hv
  obtain ⟨_h4,h3,h2,h1,h0,p1,p2,p3,p4,p5,_⟩ := hv
  have h3' : t (h-3)=true := by convert h3 using 1 <;> congr 1 <;> omega
  have h2' : t (h-2)=false := by convert h2 using 1 <;> congr 1 <;> omega
  have h1' : t (h-1)=true := by convert h1 using 1 <;> congr 1 <;> omega
  have h0' : t h=true := by convert h0 using 1 <;> congr 1 <;> omega
  have p1' : t (h+1)=false := by convert p1 using 1 <;> congr 1 <;> omega
  have p2' : t (h+2)=false := by convert p2 using 1 <;> congr 1 <;> omega
  have p3' : t (h+3)=false := by convert p3 using 1 <;> congr 1 <;> omega
  have p4' : t (h+4)=false := by convert p4 using 1 <;> congr 1 <;> omega
  have p5' : t (h+5)=false := by convert p5 using 1 <;> congr 1 <;> omega
  have a := dispatch_93_to166 h t h3' h2' h1'
  have b1 := oneSeg machine _ _ (unchanged_right 166 165 true h t (by decide) h0')
  have b2 := oneSeg machine _ _ (unchanged_right 165 164 false (h+1) t (by decide) p1')
  have b3 := oneSeg machine _ _ (unchanged_right 164 163 false (h+2) t (by decide) p2')
  have b4 := oneSeg machine _ _ (unchanged_right 163 215 false (h+3) t (by decide) p3')
  have b5 := oneSeg machine _ _ (unchanged_right 215 182 false (h+4) t (by decide) p4')
  have b6 := oneSeg machine _ _ (unchanged_right 182 62 false (h+5) t (by decide) p5')
  have s1 := segAdd machine _ _ _ 3 1 a b1
  have s2 := segAdd machine _ _ _ 4 1 s1 b2
  have s2' : silentSegment machine (cfg 93 (h-3) t) (cfg 164 (h+2) t) 5 := by simpa [Int.add_assoc] using s2
  have s3 := segAdd machine _ _ _ 5 1 s2' b3
  have s3' : silentSegment machine (cfg 93 (h-3) t) (cfg 163 (h+3) t) 6 := by simpa [Int.add_assoc] using s3
  have s4 := segAdd machine _ _ _ 6 1 s3' b4
  have s4' : silentSegment machine (cfg 93 (h-3) t) (cfg 215 (h+4) t) 7 := by simpa [Int.add_assoc] using s4
  have s5 := segAdd machine _ _ _ 7 1 s4' b5
  have s5' : silentSegment machine (cfg 93 (h-3) t) (cfg 182 (h+5) t) 8 := by simpa [Int.add_assoc] using s5
  have all := segAdd machine _ _ _ 8 1 s5' b6
  simpa [Int.add_assoc] using all

#print axioms next_leaf
#print axioms next_retained
#print axioms next_graph_instruction
#print axioms next_path_walk
#print axioms carry_to_next_path
#print axioms dispatch_next_path
end Shared.Beeping.NPcoNP.NativeFirstNextPath
