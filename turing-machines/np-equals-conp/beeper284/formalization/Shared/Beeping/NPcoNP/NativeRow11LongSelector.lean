import Shared.Beeping.NPcoNP.NativeRow11LongPrepare
import Shared.Beeping.NPcoNP.Native62Redispatch

/-! Finite state-83 selector returns for the long row-11 preparation. -/
namespace Shared.Beeping.NPcoNP.NativeRow11LongSelector
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeFirstZeroNext
open Shared.Beeping.NPcoNP.NativeRow10ZeroCarry
open Shared.Beeping.NPcoNP.NativeRow11LongPrepare
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- With the shortest long gap, the selector returns without changing tape. -/
theorem selector_base (h : Int) (t : Int → Bool)
    (path : Holds t (h-4) row11Path) (left : ∀ q, q<h-4 → t q=false) :
    silentSegment machine (cfg 83 (h+9) t) (cfg 93 (h-3) t) 32 := by
  have hv := path
  simp only [row11Path,Holds] at hv
  obtain ⟨a4,a3,a2,a1,a0,b1,b2,b3,b4,b5,b6,b7,b8,b9,_⟩ := hv
  let ks : List Nat := [0,0,0,4,0,2,2] ++ List.replicate 7 0
  have hw : downHolds t (h+9) (blocks ks ++ []) := by
    dsimp [ks,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | (convert a4 using 1 <;> congr 1 <;> omega) | (convert a3 using 1 <;> congr 1 <;> omega) |
      (convert a2 using 1 <;> congr 1 <;> omega) | (convert a1 using 1 <;> congr 1 <;> omega) |
      (convert a0 using 1 <;> congr 1 <;> omega) | (convert b1 using 1 <;> congr 1 <;> omega) |
      (convert b2 using 1 <;> congr 1 <;> omega) | (convert b3 using 1 <;> congr 1 <;> omega) |
      (convert b4 using 1 <;> congr 1 <;> omega) | (convert b5 using 1 <;> congr 1 <;> omega) |
      (convert b6 using 1 <;> congr 1 <;> omega) | (convert b7 using 1 <;> congr 1 <;> omega) |
      (convert b8 using 1 <;> congr 1 <;> omega) | (convert b9 using 1 <;> congr 1 <;> omega) |
      (apply left; omega)
  have hs := (chain_blocks chain83 ks (h+9) t [] (by decide) hw).2
  have hs' : silentSegment machine (cfg 83 (h+9) t) (cfg 92 (h-13) t) 22 := by
    have he : h+9-22=h-13 := by omega
    simpa [ks,blocks,List.replicate_succ,he] using hs
  have hz : ∀ i : Nat, i<9 → t ((h-13)+(i : Int))=false := by
    intro i hi; apply left; omega
  have ho : t ((h-13)+(9 : Int))=true := by
    have he : h-13+9=h-4 := by omega
    simpa only [he] using a4
  have hr := scan92_exact 9 (h-13) t hz ho
  have all := segAdd machine _ _ _ 22 10 hs' hr
  convert all using 1 <;> congr 1 <;> omega

/-- A nonempty filled prefix contributes one selector step per cell. -/
theorem selector_many (h : Int) (m : Nat) (t : Int → Bool)
    (path : Holds t (h-4) row11Path) (left : ∀ q, q<h-4 → t q=false)
    (h10 : t (h+10)=true) (h11 : t (h+11)=false) (h12 : t (h+12)=false)
    (ones : ∀ q, h+13≤q → q≤h+12+(m : Int) → t q=true) :
    silentSegment machine (cfg 83 (h+12+(m : Int)) t) (cfg 93 (h-3) t) (m+31) := by
  have hv := path
  simp only [row11Path,Holds] at hv
  obtain ⟨a4,a3,a2,a1,a0,b1,b2,b3,b4,b5,b6,b7,b8,b9,_⟩ := hv
  let ks : List Nat := [0,1,0,0,4,0,2,2] ++ List.replicate 5 0
  have htail : downHolds t (h+11) (blocks ks ++ []) := by
    dsimp [ks,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | (convert a4 using 1 <;> congr 1 <;> omega) | (convert a3 using 1 <;> congr 1 <;> omega) |
      (convert a2 using 1 <;> congr 1 <;> omega) | (convert a1 using 1 <;> congr 1 <;> omega) |
      (convert a0 using 1 <;> congr 1 <;> omega) | (convert b1 using 1 <;> congr 1 <;> omega) |
      (convert b2 using 1 <;> congr 1 <;> omega) | (convert b3 using 1 <;> congr 1 <;> omega) |
      (convert b4 using 1 <;> congr 1 <;> omega) | (convert b5 using 1 <;> congr 1 <;> omega) |
      (convert b6 using 1 <;> congr 1 <;> omega) | (convert b7 using 1 <;> congr 1 <;> omega) |
      (convert b8 using 1 <;> congr 1 <;> omega) | (convert b9 using 1 <;> congr 1 <;> omega) |
      (convert h10 using 1 <;> congr 1 <;> omega) | (convert h11 using 1 <;> congr 1 <;> omega) |
      (apply left; omega)
  have hfirst : downHolds t (h+12+(m : Int)) (List.replicate m true ++ false :: (blocks ks ++ [])) := by
    apply down_ones
    · intro i hi
      apply ones <;> omega
    · have he : h+12+(m : Int)-(m : Int)=h+12 := by omega
      rw [he]
      change t (h+12)=false ∧ downHolds t (h+12-1) (blocks ks ++ [])
      have he' : h+12-1=h+11 := by omega
      exact ⟨h12,by simpa only [he'] using htail⟩
  have hs1 := (scan_block ScanRow.r83 m (h+12+(m : Int)) t (blocks ks ++ []) hfirst).2
  have hs1' : silentSegment machine (cfg 83 (h+12+(m : Int)) t) (cfg 82 (h+11) t) (m+1) := by
    have he : h+12+(m : Int)-((m+1 : Nat) : Int)=h+11 := by push_cast; omega
    simpa only [he] using hs1
  have hs2 := (chain_blocks chain82 ks (h+11) t [] (by decide) htail).2
  have hs2' : silentSegment machine (cfg 82 (h+11) t) (cfg 92 (h-11) t) 22 := by
    have he : h+11-22=h-11 := by omega
    simpa [ks,blocks,List.replicate_succ,he] using hs2
  have hz : ∀ i : Nat, i<7 → t ((h-11)+(i : Int))=false := by
    intro i hi; apply left; omega
  have ho : t ((h-11)+(7 : Int))=true := by
    have he : h-11+7=h-4 := by omega
    simpa only [he] using a4
  have hs3 := scan92_exact 7 (h-11) t hz ho
  have hs12 := segAdd machine _ _ _ (m+1) 22 hs1' hs2'
  have all := segAdd machine _ _ _ (m+1+22) 8 hs12 hs3
  convert all using 1 <;> congr 1 <;> omega

#print axioms selector_base
#print axioms selector_many
end Shared.Beeping.NPcoNP.NativeRow11LongSelector
