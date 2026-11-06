import Shared.Beeping.NPcoNP.NativeRows8To11
import Shared.Beeping.NPcoNP.Native64Prepare

/-! Literal row-11 dispatch and the state-66 control-entry branches. -/
namespace Shared.Beeping.NPcoNP.NativeRow11Dispatch
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeFirstNextPath
open Shared.Beeping.NPcoNP.NativeRow10ZeroCarry
open Shared.Beeping.NPcoNP.NativeRows8To11
open Shared.Beeping.NPcoNP.NativeRow8Cycles
open Shared.Beeping.NPcoNP.NativeRow8GraphCycles
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Native64Prepare
open Shared.Beeping.NPcoNP.Native54Prepare
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

theorem dispatch_row11_path (h : Int) (t : Int → Bool) (hw : Holds t (h-4) row11Path) :
    silentSegment machine (cfg 93 (h-3) t) (cfg 66 (h+10) t) 13 := by
  have hv := hw
  simp only [row11Path,Holds] at hv
  obtain ⟨_h4,h3,h2,h1,h0,p1,p2,p3,p4,p5,p6,p7,p8,p9,_⟩ := hv
  have h3' : t (h-3)=true := by convert h3 using 1 <;> congr 1 <;> omega
  have h2' : t (h-2)=false := by convert h2 using 1 <;> congr 1 <;> omega
  have h1' : t (h-1)=true := by convert h1 using 1 <;> congr 1 <;> omega
  have h0' : t h=true := by convert h0 using 1 <;> congr 1 <;> omega
  have p1' : t (h+1)=false := by convert p1 using 1 <;> congr 1 <;> omega
  have p2' : t (h+2)=false := by convert p2 using 1 <;> congr 1 <;> omega
  have p3' : t (h+3)=true := by convert p3 using 1 <;> congr 1 <;> omega
  have p4' : t (h+4)=true := by convert p4 using 1 <;> congr 1 <;> omega
  have p5' : t (h+5)=true := by convert p5 using 1 <;> congr 1 <;> omega
  have p6' : t (h+6)=true := by convert p6 using 1 <;> congr 1 <;> omega
  have p7' : t (h+7)=false := by convert p7 using 1 <;> congr 1 <;> omega
  have p8' : t (h+8)=false := by convert p8 using 1 <;> congr 1 <;> omega
  have p9' : t (h+9)=false := by convert p9 using 1 <;> congr 1 <;> omega
  have a := dispatch_93_to166 h t h3' h2' h1'
  have b1 := oneSeg machine _ _ (unchanged_right 166 165 true h t (by decide) h0')
  have b2 := oneSeg machine _ _ (unchanged_right 165 164 false (h+1) t (by decide) p1')
  have b3 := oneSeg machine _ _ (unchanged_right 164 163 false (h+2) t (by decide) p2')
  have b4 := oneSeg machine _ _ (unchanged_right 163 162 true (h+3) t (by decide) p3')
  have b5 := oneSeg machine _ _ (unchanged_right 162 161 true (h+4) t (by decide) p4')
  have b6 := oneSeg machine _ _ (unchanged_right 161 160 true (h+5) t (by decide) p5')
  have b7 := oneSeg machine _ _ (unchanged_right 160 159 true (h+6) t (by decide) p6')
  have b8 := oneSeg machine _ _ (unchanged_right 159 124 false (h+7) t (by decide) p7')
  have b9 := oneSeg machine _ _ (unchanged_right 124 113 false (h+8) t (by decide) p8')
  have b10 := oneSeg machine _ _ (unchanged_right 113 66 false (h+9) t (by decide) p9')
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
  have s6' : silentSegment machine (cfg 93 (h-3) t) (cfg 160 (h+6) t) 9 := by simpa [Int.add_assoc] using s6
  have s7 := segAdd machine _ _ _ 9 1 s6' b7
  have s7' : silentSegment machine (cfg 93 (h-3) t) (cfg 159 (h+7) t) 10 := by simpa [Int.add_assoc] using s7
  have s8 := segAdd machine _ _ _ 10 1 s7' b8
  have s8' : silentSegment machine (cfg 93 (h-3) t) (cfg 124 (h+8) t) 11 := by simpa [Int.add_assoc] using s8
  have s9 := segAdd machine _ _ _ 11 1 s8' b9
  have s9' : silentSegment machine (cfg 93 (h-3) t) (cfg 113 (h+9) t) 12 := by simpa [Int.add_assoc] using s9
  have all := segAdd machine _ _ _ 12 1 s9' b10
  simpa [Int.add_assoc] using all

/-- The state-66 one branch starts the next bank scan without writing. -/
theorem step66_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 66 h t)=(cfg 281 (h+1) t,false) := by
  have row : machine.table.row 66 true=⟨true,.right,281,false⟩ := by decide
  have hw : (⟨66,h,t⟩ : Config 284).write true=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

/-- The zero branch starts the same finite preparation as state 64. -/
theorem step66_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 66 h t)=(cfg 9 (h+1) (setAt h t),false) := by
  have row : machine.table.row 66 false=⟨true,.right,9,false⟩ := by decide
  have hw : (⟨66,h,t⟩ : Config 284).write true=setAt h t := rfl
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

theorem zero_prepare_to83_exact (x : Int) (t : Int → Bool) (k : Nat)
    (h0 : t x=false) (h1 : t (x+1)=false) (h2 : t (x+2)=false)
    (zeros : ∀ i : Nat, i<k → t (x+3+(i : Int))=false)
    (marker : t (x+3+(k : Int))=true) :
    let out := fillRange (setAt x t) (x+3) (x+3+(k : Int))
    let head := if k=0 then x-1 else x+3+(k : Int)-2
    let duration := if k=0 then 7 else k+5
    silentSegment machine (cfg 66 x t) (cfg 83 head out) duration := by
  dsimp only
  let out := fillRange (setAt x t) (x+3) (x+3+(k : Int))
  let head := if k=0 then x-1 else x+3+(k : Int)-2
  let duration := if k=0 then 7 else k+5
  have hp : 0<duration := by dsimp [duration]; split_ifs <;> omega
  have hd : duration-1+1=duration := by omega
  have he : machine.step (cfg 64 x t)=machine.step (cfg 66 x t) := by
    rw [step64_zero x t h0,step66_zero x t h0]
  have hs : silentSegment machine (cfg 64 x t) (cfg 83 head out) (duration-1+1) := by
    rw [hd]
    exact Native64Prepare.zero_prepare_to83_exact x t k h0 h1 h2 zeros marker
  have hr := (replace_equal_first machine (cfg 64 x t) (cfg 66 x t)
    (cfg 83 head out) (duration-1) he).mp hs
  simpa only [hd,out,head,duration] using hr

/-- The previously proved row-8 and row-10 phases continue through all
13 literal row-11 dispatch transitions with no additional event. -/
theorem countdowns_to_state66 (n : Nat) (h separator : Int) (t : Int → Bool)
    (a b : Nat) (pre : List Nat) (v : Nat) (post : List Nat) (z : Nat)
    (rest : List Nat) (bank : Bank 12) (hlen : pre.length=4)
    (ready : NativeRow8Cycles.Ready h separator t a b (pre++v::post) n z rest bank) :
    let selected := cycleBanks n bank
    ∃ (k : Nat) (out : Int → Bool), n+16≤k ∧ CyclesGood n bank ∧
      target.system.step ⟨8,selected⟩=(⟨10,selected⟩,[]) ∧
      (target.system.advance ⟨10,selected⟩ (v+1)).state=11 ∧
      target.system.wordFrom ⟨10,selected⟩ (v+1)=[] ∧
      Holds out (h-4) row11Path ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 66 (h+10) out) k := by
  obtain ⟨k,out,hk,hgood,hzero,hs,he,hpath,_,hseg⟩ :=
    row8_then_row10_countdowns n h separator t a b pre v post z rest bank hlen ready
  have hd := dispatch_row11_path h out hpath
  exact ⟨k+13,out,by omega,hgood,hzero,hs,he,hpath,segAdd machine _ _ _ k 13 hseg hd⟩

#print axioms dispatch_row11_path
#print axioms step66_one
#print axioms zero_prepare_to83_exact
#print axioms countdowns_to_state66
end Shared.Beeping.NPcoNP.NativeRow11Dispatch
