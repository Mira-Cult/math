import Shared.Beeping.NPcoNP.NativeFourthNextPath

/-! Literal carry, selector and dispatch to the next positive-branch path.
All tape layouts are supplied; reachability is a separate theorem. -/
namespace Shared.Beeping.NPcoNP.NativeFifthNextPath
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeBeepZeroReturn
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeFirstNextPath
open Shared.Beeping.NPcoNP.NativeFourthNextPath
open Shared.Beeping.NPcoNP.NativeSelectorParserGeneric
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

def sixthPath : List Bool := [true,true,false,true,true,false,false,true,true,false,true,false]

theorem sixth_leaf : traceState557.acc.leaves[13]? =
    some (sixthPath,"3.$coalesced.0.inc") := by decide

theorem sixth_retained : producerNumbering.map[13]?=some (some 9) := by decide

theorem sixth_path_walk : PreparedWalk sixthPath (.op "3.$coalesced.0.inc") := by
  refine ⟨[true,true,false,false,true,true,false,true,false],rfl,?_⟩
  apply follow_sound producerGrammar [true,true,false,false,true,true,false,true,false] (.node producerGrammar.root)
  decide

theorem sixth_path_parse (t : Int → Bool) (h : Int) (hw : Holds t h sixthPath) :
    parseForward 52 t h=some ("3.$coalesced.0.inc",12) := by
  apply (parseForward_iff t h "3.$coalesced.0.inc" 12).2
  exact ⟨sixthPath,sixth_path_walk,rfl,hw⟩

theorem sixth_selector (h : Int) (t : Int → Bool)
    (word : Holds t (h-4) sixthPath) (left : ∀ q, q<h-4 → t q=false) :
    silentSegment machine (cfg 83 (h+5) t) (cfg 93 (h-3) t) 32 := by
  have hv := word
  simp only [sixthPath,Holds] at hv
  obtain ⟨hm4,hm3,hm2,hm1,h0,hp1,hp2,hp3,hp4,hp5,_⟩ := hv
  have hm3' : t (h-3)=true := by convert hm3 using 1 <;> congr 1 <;> omega
  have hm2' : t (h-2)=false := by convert hm2 using 1 <;> congr 1 <;> omega
  have hm1' : t (h-1)=true := by convert hm1 using 1 <;> congr 1 <;> omega
  have h0' : t h=true := by convert h0 using 1 <;> congr 1 <;> omega
  have hp1' : t (h+1)=false := by convert hp1 using 1 <;> congr 1 <;> omega
  have hp2' : t (h+2)=false := by convert hp2 using 1 <;> congr 1 <;> omega
  have hp3' : t (h+3)=true := by convert hp3 using 1 <;> congr 1 <;> omega
  have hp4' : t (h+4)=true := by convert hp4 using 1 <;> congr 1 <;> omega
  have hp5' : t (h+5)=false := by convert hp5 using 1 <;> congr 1 <;> omega
  let ks : List Nat := [0,2,0,2,2] ++ List.replicate 9 0
  have hw : downHolds t (h+5) (blocks ks ++ []) := by
    dsimp [ks,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | exact hp5' | (convert hp4' using 1 <;> congr 1 <;> omega) |
      (convert hp3' using 1 <;> congr 1 <;> omega) | (convert hp2' using 1 <;> congr 1 <;> omega) |
      (convert hp1' using 1 <;> congr 1 <;> omega) | (convert h0' using 1 <;> congr 1 <;> omega) |
      (convert hm1' using 1 <;> congr 1 <;> omega) | (convert hm2' using 1 <;> congr 1 <;> omega) |
      (convert hm3' using 1 <;> congr 1 <;> omega) | (convert hm4 using 1 <;> congr 1 <;> omega) |
      (apply left; omega)
  have hb := selector_to_parser t (h+5) (h-4) ks sixthPath
    "3.$coalesced.0.inc" (by decide) hw (by simp [ks,blocks]; omega)
    left hm4 sixth_path_walk word
  have hd : (h-4-(h+5-20)).toNat=11 := by congr 1 <;> omega
  have he : h-4+1=h-3 := by omega
  simpa [ks,blocks,List.replicate_succ,sixthPath,hd,he] using hb.2.1

/-- The path after the positive decrement dispatches in eleven literal,
silent steps to state 51 and leaves the whole tape unchanged. -/
theorem dispatch_sixth_path (h : Int) (t : Int → Bool) (hw : Holds t (h-4) sixthPath) :
    silentSegment machine (cfg 93 (h-3) t) (cfg 51 (h+8) t) 11 := by
  have hv := hw
  simp only [sixthPath,Holds] at hv
  obtain ⟨_h4,h3,h2,h1,h0,p1,p2,p3,p4,p5,p6,p7,_⟩ := hv
  have h3' : t (h-3)=true := by convert h3 using 1 <;> congr 1 <;> omega
  have h2' : t (h-2)=false := by convert h2 using 1 <;> congr 1 <;> omega
  have h1' : t (h-1)=true := by convert h1 using 1 <;> congr 1 <;> omega
  have h0' : t h=true := by convert h0 using 1 <;> congr 1 <;> omega
  have p1' : t (h+1)=false := by convert p1 using 1 <;> congr 1 <;> omega
  have p2' : t (h+2)=false := by convert p2 using 1 <;> congr 1 <;> omega
  have p3' : t (h+3)=true := by convert p3 using 1 <;> congr 1 <;> omega
  have p4' : t (h+4)=true := by convert p4 using 1 <;> congr 1 <;> omega
  have p5' : t (h+5)=false := by convert p5 using 1 <;> congr 1 <;> omega
  have p6' : t (h+6)=true := by convert p6 using 1 <;> congr 1 <;> omega
  have p7' : t (h+7)=false := by convert p7 using 1 <;> congr 1 <;> omega
  have a := dispatch_93_to166 h t h3' h2' h1'
  have b1 := oneSeg machine _ _ (unchanged_right 166 165 true h t (by decide) h0')
  have b2 := oneSeg machine _ _ (unchanged_right 165 164 false (h+1) t (by decide) p1')
  have b3 := oneSeg machine _ _ (unchanged_right 164 163 false (h+2) t (by decide) p2')
  have b4 := oneSeg machine _ _ (unchanged_right 163 162 true (h+3) t (by decide) p3')
  have b5 := oneSeg machine _ _ (unchanged_right 162 161 true (h+4) t (by decide) p4')
  have b6 := oneSeg machine _ _ (unchanged_right 161 248 false (h+5) t (by decide) p5')
  have b7 := oneSeg machine _ _ (unchanged_right 248 237 true (h+6) t (by decide) p6')
  have b8 := oneSeg machine _ _ (unchanged_right 237 51 false (h+7) t (by decide) p7')
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
  have s7 := segAdd machine _ _ _ 9 1 s6' b7
  have s7' : silentSegment machine (cfg 93 (h-3) t) (cfg 237 (h+7) t) 10 := by simpa [Int.add_assoc] using s7
  have all := segAdd machine _ _ _ 10 1 s7' b8
  simpa [Int.add_assoc] using all

#print axioms sixth_leaf
#print axioms sixth_retained
#print axioms sixth_selector
#print axioms dispatch_sixth_path
end Shared.Beeping.NPcoNP.NativeFifthNextPath
