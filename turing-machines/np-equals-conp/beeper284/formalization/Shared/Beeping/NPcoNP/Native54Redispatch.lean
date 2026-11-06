import Shared.Beeping.NPcoNP.Native54Prepare
import Shared.Beeping.NPcoNP.Native50Redispatch

/-! Finite, conditional state-54 preparation and redispatch. The statement
uses a supplied path and marker; it does not assert blank-start reachability or
that the subsequent scanner completes its register operation. -/
namespace Shared.Beeping.NPcoNP.Native54Redispatch
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeFirstZeroNext
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.Native54Prepare
open Shared.Beeping.NPcoNP.NativeFourthNextPath
open Shared.Beeping.NPcoNP.NativeSelectorParserGeneric
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

theorem step54_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 54 h t)=(cfg 273 (h+1) t,false) := by
  have row : machine.table.row 54 true=⟨true,.right,273,false⟩ := by decide
  have hw : (⟨54,h,t⟩ : Config 284).write true=t := by
    rw [←ht]
    exact NativeHalfRows.write_current _
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

/-- The actual selector rediscovers the prepared path after the state-54
marker and run are installed. -/
theorem selector_prepared (h : Int) (r : Nat) (t : Int → Bool)
    (hw : Holds t (h-4) fifthPath) (left : ∀ q, q<h-4 → t q=false)
    (h8 : t (h+8)=false) (h9 : t (h+9)=false) :
    let u := fillRange (setAt (h+7) t) (h+10) (h+11+(r : Int))
    silentSegment machine (cfg 83 (h+9+(r : Int)) u) (cfg 93 (h-3) u) (r+30) := by
  dsimp only
  let u := fillRange (setAt (h+7) t) (h+10) (h+11+(r : Int))
  have hf : ∀ q, q<h+10 → q≠h+7 → u q=t q := by
    intro q hq hne
    have hn : ¬ (h+10≤q ∧ q<h+11+(r : Int)) := by omega
    simp [u,fillRange,setAt,hn,hne]
  have hv := hw
  simp only [fifthPath,Holds] at hv
  obtain ⟨hm4,hm3,hm2,hm1,h0,p1,p2,p3,p4,p5,p6,_⟩ := hv
  have hm3' : t (h-3)=true := by convert hm3 using 1 <;> congr 1 <;> omega
  have hm2' : t (h-2)=false := by convert hm2 using 1 <;> congr 1 <;> omega
  have hm1' : t (h-1)=true := by convert hm1 using 1 <;> congr 1 <;> omega
  have h0' : t h=true := by convert h0 using 1 <;> congr 1 <;> omega
  have p1' : t (h+1)=false := by convert p1 using 1 <;> congr 1 <;> omega
  have p2' : t (h+2)=false := by convert p2 using 1 <;> congr 1 <;> omega
  have p3' : t (h+3)=true := by convert p3 using 1 <;> congr 1 <;> omega
  have p4' : t (h+4)=true := by convert p4 using 1 <;> congr 1 <;> omega
  have p5' : t (h+5)=false := by convert p5 using 1 <;> congr 1 <;> omega
  have p6' : t (h+6)=false := by convert p6 using 1 <;> congr 1 <;> omega
  have a4 : u (h-4)=true := by rw [hf _ (by omega) (by omega)]; exact hm4
  have a3 : u (h-3)=true := by rw [hf _ (by omega) (by omega)]; exact hm3'
  have a2 : u (h-2)=false := by rw [hf _ (by omega) (by omega)]; exact hm2'
  have a1 : u (h-1)=true := by rw [hf _ (by omega) (by omega)]; exact hm1'
  have a0 : u h=true := by rw [hf _ (by omega) (by omega)]; exact h0'
  have b1 : u (h+1)=false := by rw [hf _ (by omega) (by omega)]; exact p1'
  have b2 : u (h+2)=false := by rw [hf _ (by omega) (by omega)]; exact p2'
  have b3 : u (h+3)=true := by rw [hf _ (by omega) (by omega)]; exact p3'
  have b4 : u (h+4)=true := by rw [hf _ (by omega) (by omega)]; exact p4'
  have b5 : u (h+5)=false := by rw [hf _ (by omega) (by omega)]; exact p5'
  have b6 : u (h+6)=false := by rw [hf _ (by omega) (by omega)]; exact p6'
  have b7 : u (h+7)=true := by simp [u,fillRange,setAt]
  have b8 : u (h+8)=false := by rw [hf _ (by omega) (by omega)]; exact h8
  have b9 : u (h+9)=false := by rw [hf _ (by omega) (by omega)]; exact h9
  have hleft : ∀ q, q<h-4 → u q=false := by
    intro q hq
    rw [hf q (by omega) (by omega)]
    exact left q hq
  have hrun : ∀ q, h+10≤q → q≤h+9+(r : Int) → u q=true := by
    intro q hq hq'
    have hr : h+10≤q ∧ q<h+11+(r : Int) := by omega
    simp [u,fillRange,hr]
  let rest : List Nat := [0,1,0,2,0,2,2] ++ List.replicate 6 0
  have htail : downHolds u (h+8) (blocks rest ++ []) := by
    dsimp [rest,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | exact b8 | (convert b7 using 1 <;> congr 1 <;> omega) |
      (convert b6 using 1 <;> congr 1 <;> omega) | (convert b5 using 1 <;> congr 1 <;> omega) |
      (convert b4 using 1 <;> congr 1 <;> omega) | (convert b3 using 1 <;> congr 1 <;> omega) |
      (convert b2 using 1 <;> congr 1 <;> omega) | (convert b1 using 1 <;> congr 1 <;> omega) |
      (convert a0 using 1 <;> congr 1 <;> omega) | (convert a1 using 1 <;> congr 1 <;> omega) |
      (convert a2 using 1 <;> congr 1 <;> omega) | (convert a3 using 1 <;> congr 1 <;> omega) |
      (convert a4 using 1 <;> congr 1 <;> omega) | (apply hleft; omega)
  let ks := r::rest
  have hfirst : downHolds u (h+9+(r : Int)) (List.replicate r true ++ false :: (blocks rest ++ [])) := by
    apply down_ones
    · intro i hi
      apply hrun <;> omega
    · have he : h+9+(r : Int)-(r : Int)=h+9 := by omega
      rw [he]
      change u (h+9)=false ∧ downHolds u (h+9-1) (blocks rest ++ [])
      have he' : h+9-1=h+8 := by omega
      exact ⟨b9,by simpa only [he'] using htail⟩
  have hwindow : downHolds u (h+9+(r : Int)) (blocks ks ++ []) := by
    simpa [ks,blocks,List.append_assoc] using hfirst
  have hp : Holds u (h-4) fifthPath := by
    apply holds_transport t u _ _ hw
    intro q hq hq2
    have hq' : q<h+7 := by simp [fifthPath] at hq2; omega
    exact (hf q (by omega) (by omega)).symm
  have hlen : ks.length=14 := by simp [ks,rest]
  have hbl : (blocks ks).length=r+21 := by simp [ks,rest,blocks]
  have horder : h+9+(r : Int)-((blocks ks).length : Int) ≤ h-4 := by rw [hbl]; push_cast; omega
  have hb := selector_to_parser u (h+9+(r : Int)) (h-4) ks fifthPath
    "3.$coalesced.10.decnz" hlen hwindow horder hleft a4 fifth_path_walk hp
  have hd : (h-4-(h+9+(r : Int)-((r+21 : Nat) : Int))).toNat=8 := by
    have he : h-4-(h+9+(r : Int)-((r+21 : Nat) : Int))=8 := by push_cast; omega
    rw [he]
    decide
  rw [hbl] at hb
  have he : h-4+1=h-3 := by omega
  simpa only [hd,he,show r+21+8+1=r+30 by omega,u] using hb.2.1

#print axioms step54_one
#print axioms selector_prepared
end Shared.Beeping.NPcoNP.Native54Redispatch
