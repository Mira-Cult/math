import Shared.Beeping.NPcoNP.NativeRow13Prepare
import Shared.Beeping.NPcoNP.NativeRow11LongSelector

/-! Selector return for the prepared row-13 native-half path. -/
namespace Shared.Beeping.NPcoNP.NativeRow13Selector
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeFirstZeroNext

open Shared.Beeping.NPcoNP.NativeRow12Carry
open Shared.Beeping.NPcoNP.NativeRow13Prepare
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- The supplied prepared control window returns from state 83 to the
row-13 parser without changing the tape. -/
theorem selector_return (h : Int) (m : Nat) (t : Int → Bool)
    (path : Holds t (h-4) nextPath) (left : ∀ q, q<h-4 → t q=false)
    (h10 : t (h+10)=true) (h11 : t (h+11)=false)
    (ones : ∀ q, h+12≤q → q≤h+11+(m : Int) → t q=true) :
    silentSegment machine (cfg 83 (h+11+(m : Int)) t) (cfg 93 (h-3) t) (m+34) := by
  have hv := path
  simp only [nextPath,Holds] at hv
  obtain ⟨a4,a3,a2,a1,a0,b1,b2,b3,b4,b5,b6,b7,b8,b9,_⟩ := hv
  let ks : List Nat := [1,0,5,0,2,2] ++ List.replicate 7 0
  have htail : downHolds t (h+10) (blocks ks ++ []) := by
    dsimp [ks,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | (convert a4 using 1 <;> congr 1 <;> omega) | (convert a3 using 1 <;> congr 1 <;> omega) |
      (convert a2 using 1 <;> congr 1 <;> omega) | (convert a1 using 1 <;> congr 1 <;> omega) |
      (convert a0 using 1 <;> congr 1 <;> omega) | (convert b1 using 1 <;> congr 1 <;> omega) |
      (convert b2 using 1 <;> congr 1 <;> omega) | (convert b3 using 1 <;> congr 1 <;> omega) |
      (convert b4 using 1 <;> congr 1 <;> omega) | (convert b5 using 1 <;> congr 1 <;> omega) |
      (convert b6 using 1 <;> congr 1 <;> omega) | (convert b7 using 1 <;> congr 1 <;> omega) |
      (convert b8 using 1 <;> congr 1 <;> omega) | (convert b9 using 1 <;> congr 1 <;> omega) |
      (convert h10 using 1 <;> congr 1 <;> omega) | (apply left; omega)
  have hfirst : downHolds t (h+11+(m : Int)) (List.replicate m true ++ false :: (blocks ks ++ [])) := by
    apply down_ones
    · intro i hi
      apply ones <;> omega
    · have he : h+11+(m : Int)-(m : Int)=h+11 := by omega
      rw [he]
      change t (h+11)=false ∧ downHolds t (h+11-1) (blocks ks ++ [])
      exact ⟨h11,by simpa only [show h+11-1=h+10 by omega] using htail⟩
  have hs1 := (scan_block ScanRow.r83 m (h+11+(m : Int)) t (blocks ks ++ []) hfirst).2
  have hs1' : silentSegment machine (cfg 83 (h+11+(m : Int)) t) (cfg 82 (h+10) t) (m+1) := by
    have he : h+11+(m : Int)-((m+1 : Nat) : Int)=h+10 := by push_cast; omega
    simpa only [he] using hs1
  have hs2 := (chain_blocks chain82 ks (h+10) t [] (by decide) htail).2
  have hs2' : silentSegment machine (cfg 82 (h+10) t) (cfg 92 (h-13) t) 23 := by
    have he : h+10-23=h-13 := by omega
    simpa [ks,blocks,List.replicate_succ,he] using hs2
  have hz : ∀ i : Nat, i<9 → t ((h-13)+(i : Int))=false := by
    intro i hi; apply left; omega
  have ho : t ((h-13)+(9 : Int))=true := by
    have he : h-13+9=h-4 := by omega
    simpa only [he] using a4
  have hs3 := scan92_exact 9 (h-13) t hz ho
  have hs12 := segAdd machine _ _ _ (m+1) 23 hs1' hs2'
  have all := segAdd machine _ _ _ (m+1+23) 10 hs12 hs3
  convert all using 1 <;> congr 1 <;> omega

#print axioms selector_return
end Shared.Beeping.NPcoNP.NativeRow13Selector
