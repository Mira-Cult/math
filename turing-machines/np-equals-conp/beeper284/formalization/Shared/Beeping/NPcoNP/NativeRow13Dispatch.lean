import Shared.Beeping.NPcoNP.NativeRow11Dispatch
import Shared.Beeping.NPcoNP.NativeRow12Carry

/-! Literal dispatch of the row-13 native-half decrement-test path. -/
namespace Shared.Beeping.NPcoNP.NativeRow13Dispatch
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeFirstNextPath
open Shared.Beeping.NPcoNP.NativeRow12Carry
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- Thirteen literal transitions dispatch the prepared path to state 74;
all are silent and leave the tape unchanged. -/
theorem dispatch_row13_path (h : Int) (t : Int → Bool) (hw : Holds t (h-4) NativeRow12Carry.nextPath) :
    silentSegment machine (cfg 93 (h-3) t) (cfg 74 (h+10) t) 13 := by
  have hv := hw
  simp only [NativeRow12Carry.nextPath,Holds] at hv
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
  have p7' : t (h+7)=true := by convert p7 using 1 <;> congr 1 <;> omega
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
  have b8 := oneSeg machine _ _ (unchanged_right 159 158 true (h+7) t (by decide) p7')
  have b9 := oneSeg machine _ _ (unchanged_right 158 175 false (h+8) t (by decide) p8')
  have b10 := oneSeg machine _ _ (unchanged_right 175 74 false (h+9) t (by decide) p9')
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
  have s8' : silentSegment machine (cfg 93 (h-3) t) (cfg 158 (h+8) t) 11 := by simpa [Int.add_assoc] using s8
  have s9 := segAdd machine _ _ _ 11 1 s8' b9
  have s9' : silentSegment machine (cfg 93 (h-3) t) (cfg 175 (h+9) t) 12 := by simpa [Int.add_assoc] using s9
  have all := segAdd machine _ _ _ 12 1 s9' b10
  simpa [Int.add_assoc] using all


#print axioms dispatch_row13_path
end Shared.Beeping.NPcoNP.NativeRow13Dispatch
