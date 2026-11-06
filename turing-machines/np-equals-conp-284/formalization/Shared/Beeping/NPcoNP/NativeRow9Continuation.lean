import Shared.Beeping.NPcoNP.NativeRow9CarryPath
import Shared.Beeping.NPcoNP.NativeHalfState97Progress

/-! The literal continuation clears its two markers before row-8 selection. -/
namespace Shared.Beeping.NPcoNP.NativeRow9Continuation
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeFourthNextPath
open Shared.Beeping.NPcoNP.NativeHalfState97Progress
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeFirstNextPath
open Shared.Beeping.NPcoNP.NativeRow9CarryPath
open Shared.Beeping.NPcoNP.NativeFifthNextPath
open Shared.Beeping.NPcoNP.Grammar284PreparedTapeParser
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

theorem step237_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 237 h t)=(cfg 98 (h-1) (put t h false),false) := by
  have row : machine.table.row 237 true=⟨false,.left,98,false⟩ := by decide
  have hw : (⟨237,h,t⟩ : Config 284).write false=put t h false := rfl
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

theorem step98_one_local (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 98 h t)=(cfg 97 (h-1) (put t h false),false) := by
  have row : machine.table.row 98 true=⟨false,.left,97,false⟩ := by decide
  have hw : (⟨98,h,t⟩ : Config 284).write false=put t h false := rfl
  simp [cfg,Machine.step,ht,row,Move.apply,hw]

theorem dispatch_continuation (h : Int) (t : Int → Bool) (hw : Holds t (h-4) continuationPath) :
    silentSegment machine (cfg 93 (h-3) t)
      (cfg 83 (h+3) (put (put t (h+7) false) (h+6) false)) 14 := by
  have hv := hw
  simp only [continuationPath,Holds] at hv
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
  have p7' : t (h+7)=true := by convert p7 using 1 <;> congr 1 <;> omega
  have a := dispatch_93_to166 h t h3' h2' h1'
  have b1 := oneSeg machine _ _ (unchanged_right 166 165 true h t (by decide) h0')
  have b2 := oneSeg machine _ _ (unchanged_right 165 164 false (h+1) t (by decide) p1')
  have b3 := oneSeg machine _ _ (unchanged_right 164 163 false (h+2) t (by decide) p2')
  have b4 := oneSeg machine _ _ (unchanged_right 163 162 true (h+3) t (by decide) p3')
  have b5 := oneSeg machine _ _ (unchanged_right 162 161 true (h+4) t (by decide) p4')
  have b6 := oneSeg machine _ _ (unchanged_right 161 248 false (h+5) t (by decide) p5')
  have b7 := oneSeg machine _ _ (unchanged_right 248 237 true (h+6) t (by decide) p6')
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
  let t1 := put t (h+7) false
  let t2 := put t1 (h+6) false
  have v6 : t1 (h+6)=true := by simpa [t1,put] using p6'
  have v5 : t2 (h+5)=false := by simpa [t2,t1,put] using p5'
  have v4 : t2 (h+4)=true := by simpa [t2,t1,put] using p4'
  have b8 := oneSeg machine _ _ (step237_one (h+7) t p7')
  have s8 := segAdd machine _ _ _ 10 1 s7' b8
  have s8' : silentSegment machine (cfg 93 (h-3) t) (cfg 98 (h+6) t1) 11 := by
    have he : h+7-1=h+6 := by omega
    simpa [t1,he] using s8
  have b9 := oneSeg machine _ _ (step98_one_local (h+6) t1 v6)
  have s9 := segAdd machine _ _ _ 11 1 s8' b9
  have s9' : silentSegment machine (cfg 93 (h-3) t) (cfg 97 (h+5) t2) 12 := by
    have he : h+6-1=h+5 := by omega
    simpa [t2,he] using s9
  have b10 := oneSeg machine _ _ (step97_zero (h+5) t2 v5)
  have s10 := segAdd machine _ _ _ 12 1 s9' b10
  have s10' : silentSegment machine (cfg 93 (h-3) t) (cfg 97 (h+4) t2) 13 := by
    have he : h+5-1=h+4 := by omega
    simpa [he] using s10
  have b11 := oneSeg machine _ _ (step97_one (h+4) t2 v4)
  have all := segAdd machine _ _ _ 13 1 s10' b11
  have he : h+4-1=h+3 := by omega
  simpa [t2,t1,he] using all

/-- The continuation clears its two terminal bits, then selects and
enters the row-8 physical instruction. The bank suffix is untouched. -/
theorem continuation_to_row8 (h separator : Int) (t : Int → Bool)
    (hsep : h+8≤separator) (hw : Holds t (h-4) continuationPath)
    (left : ∀ q, q<h-4 → t q=false) :
    let u := put (put t (h+7) false) (h+6) false
    Holds u (h-4) fifthPath ∧
      (∀ q, q<h-4 → u q=false) ∧
      (∀ q, separator≤q → u q=t q) ∧
      silentSegment machine (cfg 93 (h-3) t) (cfg 54 (h+7) u) 56 := by
  dsimp only
  let u := put (put t (h+7) false) (h+6) false
  have hp : Holds u (h-4) fifthPath := by
    have hv := hw
    simp only [continuationPath,Holds] at hv
    dsimp [fifthPath,Holds,u,put]
    simp_all
    all_goals omega
  have hl : ∀ q, q<h-4 → u q=false := by
    intro q hq
    have he6 : q ≠ h+6 := by omega
    have he7 : q ≠ h+7 := by omega
    simpa [u,put,he6,he7] using left q hq
  have hf : ∀ q, separator≤q → u q=t q := by
    intro q hq
    have he6 : q ≠ h+6 := by omega
    have he7 : q ≠ h+7 := by omega
    simp [u,put,he6,he7]
  have a := dispatch_continuation h t hw
  have b := fifth_selector h u hp hl
  have c := dispatch_fifth_path h u hp
  have ab := segAdd machine _ _ _ 14 32 a b
  have abc := segAdd machine _ _ _ 46 10 ab c
  exact ⟨hp,hl,hf,abc⟩

/-- A supplied row-9 return reaches the next row-8 entry in finite
silent time, with the entire bank suffix preserved. -/
theorem carry_to_row8_entry_full (h b separator : Int) (t : Int → Bool)
    (hlong : h+12≤separator) (hw : Holds t (h-4) sixthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (h8 : t (h+8)=false) (h9 : t (h+9)=false)
    (control : ∀ q, h+10≤q → q<separator → t q=true)
    (hsep : t separator=false) (right : ∀ q, b≤q → t q=false) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧ Holds out (h-4) fifthPath ∧
      (∀ q, q<h-4 → out q=false) ∧ out (h+7)=false ∧
      (∀ q, h+7<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 (h+7) t) (cfg 54 (h+7) out) n := by
  obtain ⟨n,v,hn,hpath,_parse,hleft,hgap,hmark,hsuffix,hseg⟩ :=
    carry_to_continuation_path h b separator t hlong hw left h8 h9 control hsep right
  let out := put (put v (h+7) false) (h+6) false
  obtain ⟨hword,hl,hframe,hdispatch⟩ := continuation_to_row8 h separator v (by omega) hpath hleft
  have hg : ∀ q, h+7<q → q<separator-1 → out q=false := by
    intro q hq hq'
    have he6 : q ≠ h+6 := by omega
    have he7 : q ≠ h+7 := by omega
    simpa [out,put,he6,he7] using hgap q hq hq'
  have hm : out (separator-1)=true := by
    have he6 : separator-1 ≠ h+6 := by omega
    have he7 : separator-1 ≠ h+7 := by omega
    simpa [out,put,he6,he7] using hmark
  have hz7 : out (h+7)=false := by simp [out,put]
  refine ⟨n+56,out,by omega,hword,hl,hz7,hg,hm,?_,?_⟩
  · intro q hq
    exact (hframe q hq).trans (hsuffix q hq)
  · exact segAdd machine _ _ _ n 56 hseg hdispatch

/-- Compatibility interface which forgets the cleared entry cell. -/
theorem carry_to_row8_entry (h b separator : Int) (t : Int → Bool)
    (hlong : h+12≤separator) (hw : Holds t (h-4) sixthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (h8 : t (h+8)=false) (h9 : t (h+9)=false)
    (control : ∀ q, h+10≤q → q<separator → t q=true)
    (hsep : t separator=false) (right : ∀ q, b≤q → t q=false) :
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧ Holds out (h-4) fifthPath ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+7<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 (h+7) t) (cfg 54 (h+7) out) n := by
  obtain ⟨n,out,hn,hpath,hl,_,hg,hm,hf,hs⟩ :=
    carry_to_row8_entry_full h b separator t hlong hw left h8 h9 control hsep right
  exact ⟨n,out,hn,hpath,hl,hg,hm,hf,hs⟩

#print axioms carry_to_row8_entry_full
#print axioms carry_to_row8_entry
#print axioms continuation_to_row8
#print axioms dispatch_continuation
end Shared.Beeping.NPcoNP.NativeRow9Continuation
