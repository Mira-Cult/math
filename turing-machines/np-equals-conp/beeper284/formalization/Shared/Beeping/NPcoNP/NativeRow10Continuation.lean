import Shared.Beeping.NPcoNP.NativeRow10PositiveCarry
import Shared.Beeping.NPcoNP.NativeHalfState97Progress
import Shared.Beeping.NPcoNP.Native64ReturnTo280

/-! Positive row-10 continuation, with finite silent progress to the scanner. -/
namespace Shared.Beeping.NPcoNP.NativeRow10Continuation
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState97Progress
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeFirstNextPath
open Shared.Beeping.NPcoNP.NativeFifthZeroNextPath
open Shared.Beeping.NPcoNP.NativeRow10PositiveCarry
open Shared.Beeping.NPcoNP.Native64ReturnTo280
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

theorem step102_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 102 h t)=(cfg 97 (h-1) (put t h false),false) := by
  have row : machine.table.row 102 true=⟨false,.left,97,false⟩ := by decide
  have hw : (⟨102,h,t⟩ : Config 284).write false=put t h false := rfl
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

theorem dispatch_positive_continuation (h : Int) (t : Int → Bool) (hw : Holds t (h-4) positiveContinuationPath) :
    silentSegment machine (cfg 93 (h-3) t) (cfg 83 (h+4) (put t (h+7) false)) 13 := by
  have hv := hw
  simp only [positiveContinuationPath,Holds] at hv
  obtain ⟨_h4,h3,h2,h1,h0,p1,p2,p3,p4,p5,p6,p7,_⟩ := hv
  have h3' : t (h-3)=true := by convert h3 using 1 <;> congr 1 <;> omega
  have h2' : t (h-2)=false := by convert h2 using 1 <;> congr 1 <;> omega
  have h1' : t (h-1)=true := by convert h1 using 1 <;> congr 1 <;> omega
  have h0' : t h=true := by convert h0 using 1 <;> congr 1 <;> omega
  have p1' : t (h+1)=false := by convert p1 using 1 <;> congr 1 <;> omega
  have p2' : t (h+2)=false := by convert p2 using 1 <;> congr 1 <;> omega
  have p3' : t (h+3)=true := by convert p3 using 1 <;> congr 1 <;> omega
  have p4' : t (h+4)=true := by convert p4 using 1 <;> congr 1 <;> omega
  have p5' : t (h+5)=true := by convert p5 using 1 <;> congr 1 <;> omega
  have p6' : t (h+6)=false := by convert p6 using 1 <;> congr 1 <;> omega
  have p7' : t (h+7)=true := by convert p7 using 1 <;> congr 1 <;> omega
  have a := dispatch_93_to166 h t h3' h2' h1'
  have b1 := oneSeg machine _ _ (unchanged_right 166 165 true h t (by decide) h0')
  have b2 := oneSeg machine _ _ (unchanged_right 165 164 false (h+1) t (by decide) p1')
  have b3 := oneSeg machine _ _ (unchanged_right 164 163 false (h+2) t (by decide) p2')
  have b4 := oneSeg machine _ _ (unchanged_right 163 162 true (h+3) t (by decide) p3')
  have b5 := oneSeg machine _ _ (unchanged_right 162 161 true (h+4) t (by decide) p4')
  have b6 := oneSeg machine _ _ (unchanged_right 161 160 true (h+5) t (by decide) p5')
  have b7 := oneSeg machine _ _ (unchanged_right 160 102 false (h+6) t (by decide) p6')
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
  have s7' : silentSegment machine (cfg 93 (h-3) t) (cfg 102 (h+7) t) 10 := by simpa [Int.add_assoc] using s7
  let u := put t (h+7) false
  have p6u : u (h+6)=false := by simpa [u,put] using p6'
  have p5u : u (h+5)=true := by simpa [u,put] using p5'
  have b8 := oneSeg machine _ _ (step102_one (h+7) t p7')
  have s8 := segAdd machine _ _ _ 10 1 s7' b8
  have s8' : silentSegment machine (cfg 93 (h-3) t) (cfg 97 (h+6) u) 11 := by
    have he : h+7-1=h+6 := by omega
    simpa [u,he] using s8
  have b9 := oneSeg machine _ _ (step97_zero (h+6) u p6u)
  have s9 := segAdd machine _ _ _ 11 1 s8' b9
  have s9' : silentSegment machine (cfg 93 (h-3) t) (cfg 97 (h+5) u) 12 := by
    have he : h+6-1=h+5 := by omega
    simpa [he] using s9
  have b10 := oneSeg machine _ _ (step97_one (h+5) u p5u)
  have all := segAdd machine _ _ _ 12 1 s9' b10
  have he : h+5-1=h+4 := by omega
  simpa [u,he] using all

/-- The marker clear and redispatch take exactly 57 silent transitions. -/
theorem continuation_to_state64 (h separator : Int) (t : Int → Bool)
    (hsep : h+8≤separator) (hw : Holds t (h-4) positiveContinuationPath)
    (left : ∀ q, q<h-4 → t q=false) :
    let u := put t (h+7) false
    Holds u (h-4) zeroNextPath ∧
      (∀ q, q<h-4 → u q=false) ∧
      (∀ q, separator≤q → u q=t q) ∧
      silentSegment machine (cfg 93 (h-3) t) (cfg 64 (h+8) u) 57 := by
  dsimp only
  let u := put t (h+7) false
  have hp : Holds u (h-4) zeroNextPath := by
    have hv := hw
    simp only [positiveContinuationPath,Holds] at hv
    dsimp [zeroNextPath,Holds,u,put]
    simp_all
    all_goals omega
  have hl : ∀ q, q<h-4 → u q=false := by
    intro q hq
    have he : q ≠ h+7 := by omega
    simpa [u,put,he] using left q hq
  have hf : ∀ q, separator≤q → u q=t q := by
    intro q hq
    have he : q ≠ h+7 := by omega
    simp [u,put,he]
  have a := dispatch_positive_continuation h t hw
  have b := zero_next_selector h u hp hl
  have c := dispatch_zero_next_path h u hp
  have ab := segAdd machine _ _ _ 13 33 a b
  have abc := segAdd machine _ _ _ 46 11 ab c
  exact ⟨hp,hl,hf,abc⟩

/-- The literal positive continuation returns to the prepared row-10 scanner.
The suffix from the separator onwards is preserved. -/
theorem continuation_and_prepare (h separator : Int) (t : Int → Bool)
    (hlong : h+12≤separator) (path : Holds t (h-4) positiveContinuationPath)
    (left : ∀ q, q<h-4 → t q=false)
    (gap : ∀ q, h+7<q → q<separator-1 → t q=false)
    (marker : t (separator-1)=true) :
    let u := put t (h+7) false
    let out := fillRange (setAt (h+8) u) (h+11) (separator-1)
    ∃ k : Nat, 0<k ∧ Holds out (h-4) zeroNextPath ∧
      (∀ q, q<h-4 → out q=false) ∧ out (h+8)=true ∧
      out (h+9)=false ∧ out (h+10)=false ∧
      (∀ q, h+11≤q → q<separator → out q=true) ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 93 (h-3) t) (cfg 280 (h+9) out) k := by
  dsimp only
  let u := put t (h+7) false
  let out := fillRange (setAt (h+8) u) (h+11) (separator-1)
  obtain ⟨hp,hl,hframe,hseg⟩ := continuation_to_state64 h separator t (by omega) path left
  have hv := path
  simp only [positiveContinuationPath,Holds] at hv
  obtain ⟨_,_,_,_,_,_,_,_,_,_,p6,_,_⟩ := hv
  have h6 : t (h+6)=false := by convert p6 using 1 <;> congr 1 <;> omega
  have hg : ∀ q, h+5<q → q<separator-1 → u q=false := by
    intro q hq hq'
    by_cases hq6 : q=h+6
    · subst q
      simpa [u,put] using h6
    by_cases hq7 : q=h+7
    · subst q
      simp [u,put]
    · have ht := gap q (by omega) hq'
      simpa [u,put,hq7] using ht
  have hm : u (separator-1)=true := by
    have he : separator-1 ≠ h+7 := by omega
    simpa [u,put,he] using marker
  obtain ⟨k,hk,hpath,hleft,h8,h9,h10,hcontrol,hf,hprep⟩ :=
    prepare_and_enter_full h separator u hlong hp hl hg hm
  refine ⟨57+k,by omega,hpath,hleft,h8,h9,h10,hcontrol,?_,?_⟩
  · intro q hq
    exact (hf q hq).trans (hframe q hq)
  · exact segAdd machine _ _ _ 57 k hseg hprep

#print axioms dispatch_positive_continuation
#print axioms continuation_to_state64
#print axioms continuation_and_prepare
end Shared.Beeping.NPcoNP.NativeRow10Continuation
