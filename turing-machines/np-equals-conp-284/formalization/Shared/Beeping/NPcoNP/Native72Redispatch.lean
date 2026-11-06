import Shared.Beeping.NPcoNP.Native72Prepare
import Shared.Beeping.NPcoNP.NativeSecondNextPath

/-! Exact selector and redispatch after state-72 zero preparation, for the
retained row-5 path and arbitrary finite control-run length. No blank-start
reachability or whole-run graph refinement is assumed. -/
namespace Shared.Beeping.NPcoNP.Native72Redispatch
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeFirstZeroNext
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeSecondNextPath
open Shared.Beeping.NPcoNP.Native72Prepare
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem step72_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 72 h t)=(cfg 271 (h+1) t,false) := by
  have row : machine.table.row 72 true=⟨true,.right,271,false⟩ := by decide
  have hw : (⟨72,h,t⟩ : Config 284).write true=t := by
    rw [←ht]
    exact NativeHalfRows.write_current _
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

/-- After the state-72 preparation write and a finite fill, the literal
selector rediscovers the same prepared row-5 path. -/
theorem selector_prepared (h : Int) (r : Nat) (t : Int → Bool)
    (hw : Holds t (h-4) thirdPath) (left : ∀ q, q<h-4 → t q=false)
    (h7 : t (h+7)=false) (h8 : t (h+8)=false) :
    let u := fillRange (setAt (h+6) t) (h+9) (h+10+(r : Int))
    silentSegment machine (cfg 83 (h+8+(r : Int)) u) (cfg 93 (h-3) u) (r+29) := by
  dsimp only
  let u := fillRange (setAt (h+6) t) (h+9) (h+10+(r : Int))
  have hf : ∀ q, q<h+9 → q≠h+6 → u q=t q := by
    intro q hq hne
    have hn : ¬ (h+9≤q ∧ q<h+10+(r : Int)) := by omega
    simp [u,fillRange,setAt,hn,hne]
  have hv := hw
  simp only [thirdPath,Holds] at hv
  obtain ⟨hm4,hm3,hm2,hm1,h0,p1,p2,p3,p4,p5,_⟩ := hv
  have hm4' : t (h-4)=true := hm4
  have hm3' : t (h-3)=true := by convert hm3 using 1 <;> congr 1 <;> omega
  have hm2' : t (h-2)=false := by convert hm2 using 1 <;> congr 1 <;> omega
  have hm1' : t (h-1)=true := by convert hm1 using 1 <;> congr 1 <;> omega
  have h0' : t h=true := by convert h0 using 1 <;> congr 1 <;> omega
  have p1' : t (h+1)=false := by convert p1 using 1 <;> congr 1 <;> omega
  have p2' : t (h+2)=false := by convert p2 using 1 <;> congr 1 <;> omega
  have p3' : t (h+3)=false := by convert p3 using 1 <;> congr 1 <;> omega
  have p4' : t (h+4)=true := by convert p4 using 1 <;> congr 1 <;> omega
  have p5' : t (h+5)=false := by convert p5 using 1 <;> congr 1 <;> omega
  have a4 : u (h-4)=true := by rw [hf _ (by omega) (by omega)]; exact hm4'
  have a3 : u (h-3)=true := by rw [hf _ (by omega) (by omega)]; exact hm3'
  have a2 : u (h-2)=false := by rw [hf _ (by omega) (by omega)]; exact hm2'
  have a1 : u (h-1)=true := by rw [hf _ (by omega) (by omega)]; exact hm1'
  have a0 : u h=true := by rw [hf _ (by omega) (by omega)]; exact h0'
  have b1 : u (h+1)=false := by rw [hf _ (by omega) (by omega)]; exact p1'
  have b2 : u (h+2)=false := by rw [hf _ (by omega) (by omega)]; exact p2'
  have b3 : u (h+3)=false := by rw [hf _ (by omega) (by omega)]; exact p3'
  have b4 : u (h+4)=true := by rw [hf _ (by omega) (by omega)]; exact p4'
  have b5 : u (h+5)=false := by rw [hf _ (by omega) (by omega)]; exact p5'
  have b6 : u (h+6)=true := by simp [u,fillRange,setAt]
  have b7 : u (h+7)=false := by rw [hf _ (by omega) (by omega)]; exact h7
  have b8 : u (h+8)=false := by rw [hf _ (by omega) (by omega)]; exact h8
  have hleft : ∀ q, q<h-4 → u q=false := by
    intro q hq
    rw [hf q (by omega) (by omega)]
    exact left q hq
  have hrun : ∀ q, h+9≤q → q≤h+8+(r : Int) → u q=true := by
    intro q hq hq'
    have hr : h+9≤q ∧ q<h+10+(r : Int) := by omega
    simp [u,fillRange,hr]
  let ks : List Nat := [0,1,1,0,0,2,2] ++ List.replicate 6 0
  have htail : downHolds u (h+7) (blocks ks ++ []) := by
    dsimp [ks,blocks,List.replicate_succ,downHolds]
    repeat' constructor
    all_goals first | exact b7 | (convert b6 using 1 <;> congr 1 <;> omega) |
      (convert b5 using 1 <;> congr 1 <;> omega) | (convert b4 using 1 <;> congr 1 <;> omega) |
      (convert b3 using 1 <;> congr 1 <;> omega) | (convert b2 using 1 <;> congr 1 <;> omega) |
      (convert b1 using 1 <;> congr 1 <;> omega) | (convert a0 using 1 <;> congr 1 <;> omega) |
      (convert a1 using 1 <;> congr 1 <;> omega) | (convert a2 using 1 <;> congr 1 <;> omega) |
      (convert a3 using 1 <;> congr 1 <;> omega) | (convert a4 using 1 <;> congr 1 <;> omega) |
      (apply hleft; omega)
  have hfirst : downHolds u (h+8+(r : Int)) (List.replicate r true ++ false :: (blocks ks ++ [])) := by
    apply down_ones
    · intro i hi
      apply hrun <;> omega
    · have he : h+8+(r : Int)-(r : Int)=h+8 := by omega
      rw [he]
      change u (h+8)=false ∧ downHolds u (h+8-1) (blocks ks ++ [])
      have hs : h+8-1=h+7 := by omega
      exact ⟨b8,by simpa only [hs] using htail⟩
  have hs1 := (scan_block ScanRow.r83 r (h+8+(r : Int)) u (blocks ks ++ []) hfirst).2
  have hs1' : silentSegment machine (cfg 83 (h+8+(r : Int)) u) (cfg 82 (h+7) u) (r+1) := by
    have he : h+8+(r : Int)-((r+1 : Nat) : Int)=h+7 := by push_cast; omega
    simpa only [he] using hs1
  have hs2 := (chain_blocks chain82 ks (h+7) u [] (by decide) htail).2
  have hs2' : silentSegment machine (cfg 82 (h+7) u) (cfg 92 (h-12) u) 19 := by
    have he : h+7-19=h-12 := by omega
    simpa [ks,blocks,List.replicate_succ,he] using hs2
  have hz : ∀ i : Nat, i<8 → u ((h-12)+(i : Int))=false := by
    intro i hi
    apply hleft
    omega
  have ho : u ((h-12)+(8 : Int))=true := by
    have he : h-12+8=h-4 := by omega
    simpa only [he] using a4
  have hs3 := scan92_exact 8 (h-12) u hz ho
  have hs12 := segAdd machine _ _ _ (r+1) 19 hs1' hs2'
  have all := segAdd machine _ _ _ (r+1+19) 9 hs12 hs3
  convert all using 1 <;> congr 1 <;> omega

/-- A complete silent finite preparation and redispatch. The supplied marker
bounds the zero run; the theorem records the exact final tape and duration. -/
theorem prepare_and_redispatch (h : Int) (r : Nat) (t : Int → Bool)
    (hw : Holds t (h-4) thirdPath) (left : ∀ q, q<h-4 → t q=false)
    (gap : ∀ q, h+4<q → q<h+10+(r : Int) → t q=false)
    (marker : t (h+10+(r : Int))=true) :
    let u := fillRange (setAt (h+6) t) (h+9) (h+10+(r : Int))
    (∀ q, h+10+(r : Int)≤q → u q=t q) ∧
    silentSegment machine (cfg 72 (h+6) t) (cfg 271 (h+7) u) (2*r+45) := by
  dsimp only
  let u := fillRange (setAt (h+6) t) (h+9) (h+10+(r : Int))
  have h0 : t (h+6)=false := gap _ (by omega) (by omega)
  have h1 : t (h+7)=false := gap _ (by omega) (by omega)
  have h2 : t (h+8)=false := gap _ (by omega) (by omega)
  have hz : ∀ i : Nat, i<r+1 → t (h+6+3+(i : Int))=false := by
    intro i hi
    apply gap <;> omega
  have hm : t (h+6+3+((r+1 : Nat) : Int))=true := by
    convert marker using 1 <;> congr 1 <;> push_cast <;> omega
  obtain ⟨hu,frame,hprep⟩ := zero_prepare_to83 (h+6) t (r+1) (by omega) h0
    (by simpa [Int.add_assoc] using h1) (by simpa [Int.add_assoc] using h2) hz hm
  have prep : silentSegment machine (cfg 72 (h+6) t) (cfg 83 (h+8+(r : Int)) u) (r+6) := by
    have e1 : h+10+(r : Int)-2=h+8+(r : Int) := by omega
    have e2 : h+6+3=h+9 := by omega
    have e3 : h+9+((r+1 : Nat) : Int)=h+10+(r : Int) := by push_cast; omega
    have e4 : r+1+5=r+6 := by omega
    simpa only [e2,e3,e1,e4,u] using hprep
  have sel := selector_prepared h r t hw left h1 h2
  have hp : Holds u (h-4) thirdPath := by
    apply holds_transport t u _ _ hw
    intro q hq hq2
    have hq' : q<h+6 := by simp [thirdPath] at hq2; omega
    have hn : ¬ (h+9≤q ∧ q<h+10+(r : Int)) := by omega
    simp [u,fillRange,setAt,hn,show q≠h+6 by omega]
  have hd := dispatch_third_path h u hp
  have hone : u (h+6)=true := by simp [u,fillRange,setAt]
  have he := oneSeg machine _ _ (step72_one (h+6) u hone)
  have a := segAdd machine _ _ _ (r+6) (r+29) prep sel
  have b := segAdd machine _ _ _ (r+6+(r+29)) 9 a hd
  have c := segAdd machine _ _ _ (r+6+(r+29)+9) 1 b he
  refine ⟨?_,?_⟩
  · intro q hq
    have hn : ¬ (h+9≤q ∧ q<h+10+(r : Int)) := by omega
    simp [u,fillRange,setAt,hn,show q≠h+6 by omega]
  · have et : r+6+(r+29)+9+1=2*r+45 := by omega
    have eh : h+6+1=h+7 := by omega
    simpa only [et,eh] using c

#print axioms prepare_and_redispatch
#print axioms selector_prepared
end Shared.Beeping.NPcoNP.Native72Redispatch
