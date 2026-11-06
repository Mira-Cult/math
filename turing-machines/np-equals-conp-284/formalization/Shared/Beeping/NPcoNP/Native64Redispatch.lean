import Shared.Beeping.NPcoNP.Native64Prepare
import Shared.Beeping.NPcoNP.NativeFifthZeroNextPath
import Shared.Beeping.NPcoNP.NativeSelectorParserGeneric

/-! After the row-10 preparation, the literal selector rediscovers its
prepared path and takes state 64's one branch. These are supplied layouts. -/
namespace Shared.Beeping.NPcoNP.Native64Redispatch
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeFirstZeroNext
open Shared.Beeping.NPcoNP.NativeFifthZeroNextPath
open Shared.Beeping.NPcoNP.NativeSelectorParserGeneric
open Shared.Beeping.NPcoNP.Native64Prepare
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

/-- The nonempty-fill selector returns to the row-10 producer path. -/
theorem selector_long (h : Int) (r : Nat) (t : Int → Bool)
    (word : Holds t (h-4) zeroNextPath) (left : ∀ q, q<h-4 → t q=false)
    (h8 : t (h+8)=true) (h9 : t (h+9)=false) (h10 : t (h+10)=false)
    (run : ∀ q, h+11≤q → q≤h+10+(r : Int) → t q=true) :
    silentSegment machine (cfg 83 (h+10+(r : Int)) t) (cfg 93 (h-3) t) (r+31) := by
  have hv := word
  simp only [zeroNextPath,Holds] at hv
  obtain ⟨a4,a3,a2,a1,a0,b1,b2,b3,b4,b5,b6,b7,_⟩ := hv
  have a3' : t (h-3)=true := by convert a3 using 1 <;> congr 1 <;> omega
  have a2' : t (h-2)=false := by convert a2 using 1 <;> congr 1 <;> omega
  have a1' : t (h-1)=true := by convert a1 using 1 <;> congr 1 <;> omega
  have a0' : t h=true := by convert a0 using 1 <;> congr 1 <;> omega
  have b1' : t (h+1)=false := by convert b1 using 1 <;> congr 1 <;> omega
  have b2' : t (h+2)=false := by convert b2 using 1 <;> congr 1 <;> omega
  have b3' : t (h+3)=true := by convert b3 using 1 <;> congr 1 <;> omega
  have b4' : t (h+4)=true := by convert b4 using 1 <;> congr 1 <;> omega
  have b5' : t (h+5)=true := by convert b5 using 1 <;> congr 1 <;> omega
  have b6' : t (h+6)=false := by convert b6 using 1 <;> congr 1 <;> omega
  have b7' : t (h+7)=false := by convert b7 using 1 <;> congr 1 <;> omega
  let rest : List Nat := [0,1,0,3,0,2,2] ++ List.replicate 6 0
  have htail : downHolds t (h+9) (blocks rest ++ []) := by
    dsimp [rest,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | exact h9 | (convert h8 using 1 <;> congr 1 <;> omega) |
      (convert b7' using 1 <;> congr 1 <;> omega) | (convert b6' using 1 <;> congr 1 <;> omega) |
      (convert b5' using 1 <;> congr 1 <;> omega) | (convert b4' using 1 <;> congr 1 <;> omega) |
      (convert b3' using 1 <;> congr 1 <;> omega) | (convert b2' using 1 <;> congr 1 <;> omega) |
      (convert b1' using 1 <;> congr 1 <;> omega) | (convert a0' using 1 <;> congr 1 <;> omega) |
      (convert a1' using 1 <;> congr 1 <;> omega) | (convert a2' using 1 <;> congr 1 <;> omega) |
      (convert a3' using 1 <;> congr 1 <;> omega) | (convert a4 using 1 <;> congr 1 <;> omega) |
      (apply left; omega)
  let ks := r::rest
  have hfirst : downHolds t (h+10+(r : Int)) (List.replicate r true ++ false :: (blocks rest ++ [])) := by
    apply down_ones
    · intro i hi
      apply run <;> omega
    · have he : h+10+(r : Int)-(r : Int)=h+10 := by omega
      rw [he]
      change t (h+10)=false ∧ downHolds t (h+10-1) (blocks rest ++ [])
      exact ⟨h10,by simpa only [show h+10-1=h+9 by omega] using htail⟩
  have hwindow : downHolds t (h+10+(r : Int)) (blocks ks ++ []) := by
    simpa [ks,blocks,List.append_assoc] using hfirst
  have hlen : ks.length=14 := by simp [ks,rest]
  have hbl : (blocks ks).length=r+22 := by simp [ks,rest,blocks]
  have horder : h+10+(r : Int)-((blocks ks).length : Int) ≤ h-4 := by rw [hbl]; push_cast; omega
  have hb := selector_to_parser t (h+10+(r : Int)) (h-4) ks zeroNextPath
    "3.$coalesced.5.decnz" hlen hwindow horder left a4 zero_next_path_walk word
  have hd : (h-4-(h+10+(r : Int)-((r+22 : Nat) : Int))).toNat=8 := by
    have he : h-4-(h+10+(r : Int)-((r+22 : Nat) : Int))=8 := by push_cast; omega
    rw [he]
    decide
  rw [hbl] at hb
  have he : h-4+1=h-3 := by omega
  simpa only [hd,he,show r+22+8+1=r+31 by omega] using hb.2.1

/-- With an empty fill, state 83 starts two cells farther left, but still
finds and dispatches the same prepared producer path. -/
theorem selector_empty (h : Int) (t : Int → Bool)
    (word : Holds t (h-4) zeroNextPath) (left : ∀ q, q<h-4 → t q=false) :
    silentSegment machine (cfg 83 (h+7) t) (cfg 93 (h-3) t) 32 := by
  have hv := word
  simp only [zeroNextPath,Holds] at hv
  obtain ⟨a4,a3,a2,a1,a0,b1,b2,b3,b4,b5,b6,b7,_⟩ := hv
  have a3' : t (h-3)=true := by convert a3 using 1 <;> congr 1 <;> omega
  have a2' : t (h-2)=false := by convert a2 using 1 <;> congr 1 <;> omega
  have a1' : t (h-1)=true := by convert a1 using 1 <;> congr 1 <;> omega
  have a0' : t h=true := by convert a0 using 1 <;> congr 1 <;> omega
  have b1' : t (h+1)=false := by convert b1 using 1 <;> congr 1 <;> omega
  have b2' : t (h+2)=false := by convert b2 using 1 <;> congr 1 <;> omega
  have b3' : t (h+3)=true := by convert b3 using 1 <;> congr 1 <;> omega
  have b4' : t (h+4)=true := by convert b4 using 1 <;> congr 1 <;> omega
  have b5' : t (h+5)=true := by convert b5 using 1 <;> congr 1 <;> omega
  have b6' : t (h+6)=false := by convert b6 using 1 <;> congr 1 <;> omega
  have b7' : t (h+7)=false := by convert b7 using 1 <;> congr 1 <;> omega
  let ks : List Nat := [0,0,3,0,2,2] ++ List.replicate 8 0
  have hwindow : downHolds t (h+7) (blocks ks ++ []) := by
    dsimp [ks,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | exact b7' | (convert b6' using 1 <;> congr 1 <;> omega) |
      (convert b5' using 1 <;> congr 1 <;> omega) | (convert b4' using 1 <;> congr 1 <;> omega) |
      (convert b3' using 1 <;> congr 1 <;> omega) | (convert b2' using 1 <;> congr 1 <;> omega) |
      (convert b1' using 1 <;> congr 1 <;> omega) | (convert a0' using 1 <;> congr 1 <;> omega) |
      (convert a1' using 1 <;> congr 1 <;> omega) | (convert a2' using 1 <;> congr 1 <;> omega) |
      (convert a3' using 1 <;> congr 1 <;> omega) | (convert a4 using 1 <;> congr 1 <;> omega) |
      (apply left; omega)
  have hb := selector_to_parser t (h+7) (h-4) ks zeroNextPath
    "3.$coalesced.5.decnz" (by decide) hwindow (by simp [ks,blocks]; omega)
    left a4 zero_next_path_walk word
  have hd : (h-4-(h+7-21)).toNat=10 := by congr 1 <;> omega
  have he : h-4+1=h-3 := by omega
  simpa [ks,blocks,List.replicate_succ,hd,he] using hb.2.1

/-- The prepared row-10 one entry advances to its bank scanner. -/
theorem step64_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 64 h t)=(cfg 280 (h+1) t,false) := by
  have row : machine.table.row 64 true=⟨true,.right,280,false⟩ := by decide
  have hw : (⟨64,h,t⟩ : Config 284).write true=t := by
    rw [←ht]
    exact NativeHalfRows.write_current _
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

#print axioms selector_empty
#print axioms selector_long
#print axioms step64_one
end Shared.Beeping.NPcoNP.Native64Redispatch
