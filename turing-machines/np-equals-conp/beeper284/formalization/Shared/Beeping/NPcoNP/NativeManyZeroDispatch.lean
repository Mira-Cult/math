import Shared.Beeping.NPcoNP.NativeManyZeroTail
import Shared.Beeping.NPcoNP.NativeHalfMarkerMany

/-! Paid state-260 one dispatch through the zero-valued following bank.
A left-blank tail guarantees the two subsequent return scans finish. -/
namespace Shared.Beeping.NPcoNP.NativeManyZeroDispatch
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfMarkerMany
open Shared.Beeping.NPcoNP.NativeManyZeroTail
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

/-- The exact cleared interval is recorded. All cells at or to the right
of the bank separator survive unchanged, including the complete bank. -/
theorem dispatch260_zero_tail (p n k : Nat) (vs : List Nat) (h : Int) (t : Int → Bool)
    (head : t h=true)
    (first : Holds t (h+1) (List.replicate p true ++ [false]))
    (second : Holds t (h+(p : Int)+2) (List.replicate n true ++ [false]))
    (bank : Holds t (h+(p : Int)+(n : Int)+3) (encode (0::vs) ++ [false,false]))
    (tail : ∀ q, q≤h+(p : Int)+(n : Int)+2-(k : Int) → t q=false) :
    let u := clearAt h t
    let x := h+(p : Int)+(n : Int)+3
    ∃ m j : Nat, 0<m ∧ m≤k+2 ∧ 0<j ∧ j≤k+3 ∧
      let pos := x-1-(m : Int)
      let out := clearRange u (pos-(j : Int)+2) (pos+1)
      Holds out x (encode (0::vs) ++ [false,false]) ∧
      (∀ z, x-1≤z → out z=t z) ∧
      silentSegment machine (cfg 260 h t) (cfg 1 (pos-(j : Int)) out) (p+n+m+j+6) := by
  dsimp only
  let u := clearAt h t
  let x := h+(p : Int)+(n : Int)+3
  have hf : Holds u (h+1) (List.replicate p true ++ [false]) :=
    holds_clear_left t h (h+1) _ (by omega) first
  have hs : Holds u (h+1+(p : Int)+1) (List.replicate n true ++ [false]) := by
    have hh := holds_clear_left t h (h+(p : Int)+2) _ (by omega) second
    simpa [Int.add_assoc,Int.add_comm,Int.add_left_comm] using hh
  have hb : Holds u (h+1+(p : Int)+(n : Int)+2) (encode (0::vs) ++ [false,false]) := by
    have hh := holds_clear_left t h x _ (by dsimp [x]; omega) bank
    have he : h+1+(p : Int)+(n : Int)+2=x := by dsimp [x]; omega
    rw [he]
    exact hh
  have ht : ∀ q, q≤h+1+(p : Int)+(n : Int)+1-(k : Int) → u q=false := by
    intro q hq
    have hq' : q≤h+(p : Int)+(n : Int)+2-(k : Int) := by omega
    change (if q=h then false else t q)=false
    split_ifs
    · rfl
    · exact tail q hq'
  obtain ⟨m,j,hm,hmb,hj,hjb,hbank,hframe,hseg⟩ :=
    scans_zero_to1_left_tail p n k vs (h+1) u hf hs hb ht
  let pos := x-1-(m : Int)
  let out := clearRange u (pos-(j : Int)+2) (pos+1)
  have he : h+1+(p : Int)+(n : Int)+2=x := by dsimp [x]; omega
  rw [he] at hbank hframe hseg
  have hframe' : ∀ z, x-1≤z → out z=t z := by
    intro z hz
    have hh := hframe z hz
    change out z=u z at hh
    rw [hh]
    have hne : z≠h := by dsimp [x] at hz; omega
    simp [u,clearAt,hne]
  have hstart := oneSeg machine _ _ (step260_one h t head)
  have hall := segAdd machine _ _ _ 1 (p+n+m+j+5) hstart hseg
  have hc : 1+(p+n+m+j+5)=p+n+m+j+6 := by omega
  rw [hc] at hall
  exact ⟨m,j,hm,hmb,hj,hjb,hbank,hframe',hall⟩

#print axioms dispatch260_zero_tail
end Shared.Beeping.NPcoNP.NativeManyZeroDispatch
