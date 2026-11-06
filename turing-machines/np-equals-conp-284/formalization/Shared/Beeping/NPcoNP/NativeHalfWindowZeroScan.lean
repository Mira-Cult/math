import Shared.Beeping.NPcoNP.NativeHalfWindowBranch
import Shared.Beeping.NPcoNP.NativeHalfBankFirst

/-! Exact finite scan of zero unary blocks and the next positive value. -/
namespace Shared.Beeping.NPcoNP.NativeHalfWindowZeroScan
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState93Progress
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

theorem scan_zero_blocks (t : Int → Bool) (a : Int) (k : Nat) (tail : List Bool)
    (h : Holds t a (encode (List.replicate k 0) ++ tail)) :
    silentSegment machine (cfg 6 a t) (cfg 6 (a+((2*k : Nat) : Int)) t) (2*k) := by
  induction k generalizing a with
  | zero =>
    simp [silentSegment, WordEventSystem.advance, WordEventSystem.wordFrom]
  | succ k ih =>
    have hh : t a=true ∧ t (a+1)=false ∧ Holds t (a+2) (encode (List.replicate k 0) ++ tail) := by
      simpa [List.replicate_succ,encode,block,Holds,Int.add_assoc] using h
    have h1 := oneSeg machine _ _ (step6_one a t hh.1)
    have h2 := oneSeg machine _ _ (step7_zero (a+1) t hh.2.1)
    have h12 := segAdd machine _ _ _ 1 1 h1 h2
    have h12prime : silentSegment machine (cfg 6 a t) (cfg 6 (a+2) t) 2 := by
      simpa only [show a+1+1=a+2 by omega] using h12
    have hrest := ih (a+2) hh.2.2
    have htotal := segAdd machine _ _ _ 2 (2*k) h12prime hrest
    convert htotal using 1 <;> congr 1 <;> omega

theorem scan_one (t : Int → Bool) (a : Int) (tail : List Bool)
    (h : Holds t a (block 1 ++ tail)) :
    silentSegment machine (cfg 6 a t) (cfg 261 (a+3) t) 3 := by
  have hh : t a=true ∧ t (a+1)=true ∧ t (a+2)=false := by
    simp [block,Holds,Int.add_assoc] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  have h1 := oneSeg machine _ _ (step6_one a t hh.1)
  have h2 := oneSeg machine _ _ (step7_one (a+1) t hh.2.1)
  have h3 := oneSeg machine _ _ (step8_zero (a+2) t hh.2.2)
  have h12 := segAdd machine _ _ _ 1 1 h1 h2
  have h12prime : silentSegment machine (cfg 6 a t) (cfg 8 (a+2) t) 2 := by
    simpa only [show a+1+1=a+2 by omega] using h12
  have h123 := segAdd machine _ _ _ 2 1 h12prime h3
  convert h123 using 1 <;> congr 1 <;> omega

theorem scan_ge_two (t : Int → Bool) (a : Int) (x : Nat) (tail : List Bool)
    (h : Holds t a (block (x+2) ++ tail)) :
    silentSegment machine (cfg 6 a t) (cfg 260 (a+3) t) 3 := by
  have hh : t a=true ∧ t (a+1)=true ∧ t (a+2)=true := by
    simp [block,List.replicate_succ,Holds,Int.add_assoc] at h
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  have h1 := oneSeg machine _ _ (step6_one a t hh.1)
  have h2 := oneSeg machine _ _ (step7_one (a+1) t hh.2.1)
  have h3 := oneSeg machine _ _ (step8_one (a+2) t hh.2.2)
  have h12 := segAdd machine _ _ _ 1 1 h1 h2
  have h12prime : silentSegment machine (cfg 6 a t) (cfg 8 (a+2) t) 2 := by
    simpa only [show a+1+1=a+2 by omega] using h12
  have h123 := segAdd machine _ _ _ 2 1 h12prime h3
  convert h123 using 1 <;> congr 1 <;> omega

/-- After k zero blocks, an exact unit value dispatches to state 261. -/
theorem zero_blocks_then_one (t : Int → Bool) (a : Int) (k : Nat) (tail : List Bool)
    (h : Holds t a (encode (List.replicate k 0) ++ block 1 ++ tail)) :
    silentSegment machine (cfg 6 a t) (cfg 261 (a+((2*k : Nat) : Int)+3) t) (2*k+3) := by
  have hzero := scan_zero_blocks t a k (block 1 ++ tail) (by simpa [List.append_assoc] using h)
  have htail := holds_append_tail t a (encode (List.replicate k 0)) (block 1 ++ tail)
    (by simpa [List.append_assoc] using h)
  rw [zeros_length] at htail
  have hend := scan_one t (a+((2*k : Nat) : Int)) tail htail
  exact segAdd machine _ _ _ (2*k) 3 hzero hend

/-- After k zero blocks, a value of at least two dispatches to state 260. -/
theorem zero_blocks_then_ge_two (t : Int → Bool) (a : Int) (k x : Nat) (tail : List Bool)
    (h : Holds t a (encode (List.replicate k 0) ++ block (x+2) ++ tail)) :
    silentSegment machine (cfg 6 a t) (cfg 260 (a+((2*k : Nat) : Int)+3) t) (2*k+3) := by
  have hzero := scan_zero_blocks t a k (block (x+2) ++ tail) (by simpa [List.append_assoc] using h)
  have htail := holds_append_tail t a (encode (List.replicate k 0)) (block (x+2) ++ tail)
    (by simpa [List.append_assoc] using h)
  rw [zeros_length] at htail
  have hend := scan_ge_two t (a+((2*k : Nat) : Int)) x tail htail
  exact segAdd machine _ _ _ (2*k) 3 hzero hend

#print axioms scan_zero_blocks
#print axioms zero_blocks_then_one
#print axioms zero_blocks_then_ge_two
end Shared.Beeping.NPcoNP.NativeHalfWindowZeroScan
