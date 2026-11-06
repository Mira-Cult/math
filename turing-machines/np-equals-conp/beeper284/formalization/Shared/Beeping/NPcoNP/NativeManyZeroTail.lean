import Shared.Beeping.NPcoNP.NativeManyZeroScans
import Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress

/-! A left-blank tail supplies all delimiters for the zero-bank failure
return, without assuming a separately prepared selector shape. -/
namespace Shared.Beeping.NPcoNP.NativeManyZeroTail
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfOddReturnProgress
open Shared.Beeping.NPcoNP.NativeHalfState95Stop
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeManySelectorReturn
open Shared.Beeping.NPcoNP.NativeManyZeroEntry
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

/-- An explicit left-blank tail guarantees both returns terminate. The
complete tape is a single finite cleared interval, and the bank-side frame
is preserved. -/
theorem zero_to1_left_tail (x : Int) (t : Int → Bool) (k : Nat)
    (h0 : t x=true) (h1 : t (x+1)=false)
    (tail : ∀ p, p≤x-1-(k : Int) → t p=false) :
    ∃ m n : Nat, 0<m ∧ m≤k+2 ∧ 0<n ∧ n≤k+3 ∧
      let pos := x-1-(m : Int)
      let out := clearRange t (pos-(n : Int)+2) (pos+1)
      (∀ z, x-1≤z → out z=t z) ∧
      silentSegment machine (cfg 13 x t) (cfg 1 (pos-(n : Int)) out) (3+m+n) := by
  obtain ⟨m,hm,hmb,h25⟩ := scan25_left_zero k (x-1) t tail false
  let pos := x-1-(m : Int)
  have h25' : silentSegment machine (cfg 25 (x-1) t) (cfg 95 pos t) m := by
    simpa only [pos, Bool.false_eq_true, ↓reduceIte] using h25
  have hz : t (pos-((k+2 : Nat):Int))=false := by
    apply tail
    dsimp [pos]
    push_cast
    omega
  obtain ⟨n,hn,hnb,_hstop,_hones,h95⟩ := scan95_exact_with_stop (k+2) pos t hz
  let out := clearRange t (pos-(n : Int)+2) (pos+1)
  have hframe : ∀ z, x-1≤z → out z=t z := by
    intro z hz'
    have hnot : ¬ (pos-(n : Int)+2≤z ∧ z<pos+1) := by dsimp [pos]; omega
    change (if pos-(n : Int)+2≤z ∧ z<pos+1 then false else t z)=t z
    rw [if_neg hnot]
  have hpre := segAdd machine _ _ _ 3 m (zero_to25 x t h0 h1) h25'
  refine ⟨m,n,hm,hmb,hn,by omega,hframe,?_⟩
  exact segAdd machine _ _ _ (3+m) n hpre h95

/-- From state 15 the two paid scans and zero-bank failure branch complete
under one left-blank-tail condition, preserving the entire bank. -/
theorem scans_zero_to1_left_tail (p n k : Nat) (vs : List Nat) (h : Int) (t : Int → Bool)
    (first : Holds t h (List.replicate p true ++ [false]))
    (second : Holds t (h+(p : Int)+1) (List.replicate n true ++ [false]))
    (bank : Holds t (h+(p : Int)+(n : Int)+2) (encode (0::vs) ++ [false,false]))
    (tail : ∀ q, q≤h+(p : Int)+(n : Int)+1-(k : Int) → t q=false) :
    let x := h+(p : Int)+(n : Int)+2
    ∃ m j : Nat, 0<m ∧ m≤k+2 ∧ 0<j ∧ j≤k+3 ∧
      let pos := x-1-(m : Int)
      let out := clearRange t (pos-(j : Int)+2) (pos+1)
      Holds out x (encode (0::vs) ++ [false,false]) ∧
      (∀ z, x-1≤z → out z=t z) ∧
      silentSegment machine (cfg 15 h t) (cfg 1 (pos-(j : Int)) out) (p+n+m+j+5) := by
  dsimp only
  let x := h+(p : Int)+(n : Int)+2
  have bank' : Holds t x (block 0 ++ (encode vs ++ [false,false])) := by
    simpa [x,encode,List.append_assoc] using bank
  simp only [block_zero,List.cons_append,Holds] at bank'
  have ht : ∀ q, q≤x-1-(k : Int) → t q=false := by
    intro q hq
    apply tail
    dsimp [x] at hq
    omega
  obtain ⟨m,j,hm,hmb,hj,hjb,hframe,hzero⟩ := zero_to1_left_tail x t k bank'.1 bank'.2.1 ht
  let pos := x-1-(m : Int)
  let out := clearRange t (pos-(j : Int)+2) (pos+1)
  have hbank : Holds out x (encode (0::vs) ++ [false,false]) := by
    apply holds_transport t out x _ bank
    intro q hq _
    symm
    exact hframe q (by omega)
  have hs1 := scan15 p h t first
  have hs2 := scan11 n (h+(p : Int)+1) t second
  have h12 := segAdd machine _ _ _ (p+1) (n+1) hs1 hs2
  have h12' : silentSegment machine (cfg 15 h t) (cfg 13 x t) (p+1+(n+1)) := by
    have he : h+(p : Int)+1+(n : Int)+1=x := by dsimp [x]; omega
    simpa only [he] using h12
  have hall := segAdd machine _ _ _ (p+1+(n+1)) (3+m+j) h12' hzero
  have hc : p+1+(n+1)+(3+m+j)=p+n+m+j+5 := by omega
  rw [hc] at hall
  exact ⟨m,j,hm,hmb,hj,hjb,hbank,hframe,hall⟩

#print axioms zero_to1_left_tail
#print axioms scans_zero_to1_left_tail
end Shared.Beeping.NPcoNP.NativeManyZeroTail
