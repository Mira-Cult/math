import Shared.Beeping.NPcoNP.NativeManyBankResult

/-! Compositional state-260 one branch through the complete unary-bank shift.
All finite delimiters and the prepared bank are explicit. -/
namespace Shared.Beeping.NPcoNP.NativeManyDispatchBank
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfMarkerMany
open Shared.Beeping.NPcoNP.NativeManyComplete
open Shared.Beeping.NPcoNP.NativeManyBankResult
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000

/-- The second scan's terminating zero is the cell immediately preceding
the bank. It need not be supplied as a separate hypothesis. -/
theorem scan_delimiter (t : Int → Bool) (a : Int) (n : Nat)
    (word : Holds t a (List.replicate n true ++ [false])) :
    t (a+(n : Int))=false := by
  have h := holds_get t a (List.replicate n true ++ [false]) word n (by simp)
  simpa using h

/-- On a prepared positive bank, the state-260 one row, both paid scans,
and the entire register shift have a single exact finite silent execution.
The final tape changes only in the bank interval and at the dispatch cell. -/
theorem dispatch260_bank (p n v : Nat) (vs : List Nat) (h : Int) (t : Int → Bool)
    (head : t h=true)
    (first : Holds t (h+1) (List.replicate p true ++ [false]))
    (second : Holds t (h+(p : Int)+2) (List.replicate n true ++ [false]))
    (bank : Holds t (h+(p : Int)+(n : Int)+3) (encode ((v+1)::vs) ++ [false,false])) :
    let u := clearAt h t
    let x := h+(p : Int)+(n : Int)+3
    let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
    let f := x+2+suffix.length
    let out := spec u f (suffix.length+2)
    Holds out x (encode (v::vs) ++ [true,false,false]) ∧
    (∀ z, z≠h → (z<x ∨ f<z) → out z=t z) ∧
    silentSegment machine (cfg 260 h t) (cfg 23 (x-2) out) (p+n+2*suffix.length+11) := by
  dsimp only
  let u := clearAt h t
  let x := h+(p : Int)+(n : Int)+3
  let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  let f := x+2+((suffix.length : Nat):Int)
  let out := spec u f (suffix.length+2)
  have f1 : Holds u (h+1) (List.replicate p true ++ [false]) :=
    holds_clear_left t h (h+1) _ (by omega) first
  have f2 : Holds u (h+(p : Int)+2) (List.replicate n true ++ [false]) :=
    holds_clear_left t h _ _ (by omega) second
  have fb : Holds u x (encode ((v+1)::vs) ++ [false,false]) :=
    holds_clear_left t h x _ (by dsimp [x]; omega) bank
  have hdelim : u (x-1)=false := by
    have hd := scan_delimiter u (h+(p : Int)+2) n f2
    have he : h+(p : Int)+2+(n : Int)=x-1 := by dsimp [x]; omega
    rw [he] at hd
    exact hd
  have hw : Holds u x (encode ((v+1)::vs) ++ [false]) := by
    apply Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue.holds_prefix_word u x
      (encode ((v+1)::vs) ++ [false]) [false]
    simpa [List.append_assoc] using fb
  have hleft : u (h+1+(p : Int)+(n : Int)+1)=false := by
    have he : h+1+(p : Int)+(n : Int)+1=x-1 := by dsimp [x]; omega
    rw [he]; exact hdelim
  have f2' : Holds u (h+1+(p : Int)+1) (List.replicate n true ++ [false]) := by
    simpa [Int.add_assoc,Int.add_comm,Int.add_left_comm] using f2
  have hw' : Holds u (h+1+(p : Int)+(n : Int)+2) (encode ((v+1)::vs) ++ [false]) := by
    have he : h+1+(p : Int)+(n : Int)+2=x := by dsimp [x]; omega
    rw [he]; exact hw
  obtain ⟨hresult,hframe,_⟩ := shift_bank_with_blank v vs x u hdelim fb
  have hs := scans_then_bank p n v vs (h+1) u f1 f2' hleft hw'
  have hs' : silentSegment machine (cfg 15 (h+1) u) (cfg 23 (x-2) out)
      (p+n+2*suffix.length+10) := by
    have he : h+1+(p : Int)+(n : Int)+2=x := by dsimp [x]; omega
    simpa only [he,x,suffix,f,out] using hs
  have hstart := oneSeg machine _ _ (step260_one h t head)
  have hall := segAdd machine _ _ _ 1 (p+n+2*suffix.length+10) hstart hs'
  have hframe' : ∀ z, z≠h → (z<x ∨ f<z) → out z=t z := by
    intro z hz hr
    have hh := hframe z hr
    change out z=u z at hh
    rw [hh]
    simp [u,clearAt,hz]
  refine ⟨hresult,hframe',?_⟩
  have hc : 1+(p+n+2*suffix.length+10)=p+n+2*suffix.length+11 := by omega
  rw [hc] at hall
  simpa only [u,x,suffix,f,out] using hall

#print axioms dispatch260_bank
end Shared.Beeping.NPcoNP.NativeManyDispatchBank
