import Shared.Beeping.NPcoNP.NativeRow10PositiveCarry
import Shared.Beeping.NPcoNP.NativeRow10ZeroCarry

/-! Exact selector paths after the long row-11 bank returns. -/
namespace Shared.Beeping.NPcoNP.NativeRow11LongCarry
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeBeepZeroReturn
open Shared.Beeping.NPcoNP.NativeSelectorParserGeneric
open Shared.Beeping.NPcoNP.NativeRow10ZeroCarry
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

def zeroPath : List Bool := [true,true,false,true,true,false,false,true,true,true,true,false,true]
def positivePath : List Bool := [true,true,false,true,true,false,false,true,true,true,true,false,false,true]

theorem zero_path_walk : PreparedWalk zeroPath (.op "3.$coalesced.6.inc") := by
  refine ⟨[true,true,false,false,true,true,true,true,false,true],rfl,?_⟩
  apply follow_sound producerGrammar [true,true,false,false,true,true,true,true,false,true] (.node producerGrammar.root)
  decide

theorem positive_path_walk : PreparedWalk positivePath (.op "_continue.1") := by
  refine ⟨[true,true,false,false,true,true,true,true,false,false,true],rfl,?_⟩
  apply follow_sound producerGrammar [true,true,false,false,true,true,true,true,false,false,true] (.node producerGrammar.root)
  decide

theorem zero_selector (h : Int) (t : Int → Bool)
    (word : Holds t (h-4) zeroPath) (left : ∀ q, q<h-4 → t q=false) :
    silentSegment machine (cfg 83 (h+7) t) (cfg 93 (h-3) t) 34 := by
  have hv := word
  simp only [zeroPath,Holds] at hv
  obtain ⟨a4,a3,a2,a1,a0,b1,b2,b3,b4,b5,b6,b7,_⟩ := hv
  let ks : List Nat := [0,4,0,2,2] ++ List.replicate 9 0
  have hw : downHolds t (h+7) (blocks ks ++ []) := by
    dsimp [ks,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | (convert a4 using 1 <;> congr 1 <;> omega) |
      (convert a3 using 1 <;> congr 1 <;> omega) | (convert a2 using 1 <;> congr 1 <;> omega) |
      (convert a1 using 1 <;> congr 1 <;> omega) | (convert a0 using 1 <;> congr 1 <;> omega) |
      (convert b1 using 1 <;> congr 1 <;> omega) | (convert b2 using 1 <;> congr 1 <;> omega) |
      (convert b3 using 1 <;> congr 1 <;> omega) | (convert b4 using 1 <;> congr 1 <;> omega) |
      (convert b5 using 1 <;> congr 1 <;> omega) | (convert b6 using 1 <;> congr 1 <;> omega) |
      (convert b7 using 1 <;> congr 1 <;> omega) | (apply left; omega)
  have hb := selector_to_parser t (h+7) (h-4) ks zeroPath
    "3.$coalesced.6.inc" (by decide) hw (by simp [ks,blocks]; omega)
    left a4 zero_path_walk word
  have hd : (h-4-(h+7-22)).toNat=11 := by congr 1 <;> omega
  have he : h-4+1=h-3 := by omega
  simpa [ks,blocks,List.replicate_succ,zeroPath,hd,he] using hb.2.1

theorem positive_selector (h : Int) (t : Int → Bool)
    (word : Holds t (h-4) positivePath) (left : ∀ q, q<h-4 → t q=false) :
    silentSegment machine (cfg 83 (h+8) t) (cfg 93 (h-3) t) 33 := by
  have hv := word
  simp only [positivePath,Holds] at hv
  obtain ⟨a4,a3,a2,a1,a0,b1,b2,b3,b4,b5,b6,b7,b8,_⟩ := hv
  let ks : List Nat := [0,0,4,0,2,2] ++ List.replicate 8 0
  have hw : downHolds t (h+8) (blocks ks ++ []) := by
    dsimp [ks,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | (convert a4 using 1 <;> congr 1 <;> omega) |
      (convert a3 using 1 <;> congr 1 <;> omega) | (convert a2 using 1 <;> congr 1 <;> omega) |
      (convert a1 using 1 <;> congr 1 <;> omega) | (convert a0 using 1 <;> congr 1 <;> omega) |
      (convert b1 using 1 <;> congr 1 <;> omega) | (convert b2 using 1 <;> congr 1 <;> omega) |
      (convert b3 using 1 <;> congr 1 <;> omega) | (convert b4 using 1 <;> congr 1 <;> omega) |
      (convert b5 using 1 <;> congr 1 <;> omega) | (convert b6 using 1 <;> congr 1 <;> omega) |
      (convert b7 using 1 <;> congr 1 <;> omega) | (convert b8 using 1 <;> congr 1 <;> omega) |
      (apply left; omega)
  have hb := selector_to_parser t (h+8) (h-4) ks positivePath "_continue.1"
    (by decide) hw (by simp [ks,blocks]; omega) left a4 positive_path_walk word
  have hd : (h-4-(h+8-22)).toNat=10 := by congr 1 <;> omega
  have he : h-4+1=h-3 := by omega
  simpa [ks,blocks,List.replicate_succ,positivePath,hd,he] using hb.2.1

#print axioms zero_path_walk
#print axioms positive_path_walk
#print axioms zero_selector
#print axioms positive_selector
end Shared.Beeping.NPcoNP.NativeRow11LongCarry
