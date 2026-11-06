import Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
import Shared.Beeping.NPcoNP.NativeIncBank

/-! A variable-length unit selector, supplied scan word and bank increment.
This local composition does not assert global reachability or refinement. -/
namespace Shared.Beeping.NPcoNP.NativeUnitSelectorBankIncrement
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue

open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

/-- A unit selector with `k` leading zero blocks, followed by an explicitly
supplied finite unary scan word and bank, reaches state 23 with the first bank
value incremented. The selected tape differs from the input only at `d`. -/
theorem unit_selector_bank_increment_with_control (t : Int → Bool) (a : Int) (k y z len v : Nat)
    (ws rest : List Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ 1::y::z::ws)))
    (word : Holds t (a+((2*k : Nat):Int)+4+(y : Int)+2) (List.replicate len true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+4+(y : Int)+2+(len : Int)+1)
      (encode (v::rest) ++ [false])) :
    let d := a+((2*k : Nat):Int)+4
    let x := d+(y : Int)+2+(len : Int)+1
    ∃ e : Config 284, e.state=23 ∧ e.head=x+(((v+1)+(encode rest).length : Nat):Int) ∧
      Holds e.tape x (encode ((v+1)::rest)) ∧
      (∀ q, q<x → e.tape q=clearAt d t q) ∧
      (∀ q, q≠d → (q<x ∨ x+(((v+1)+(encode rest).length : Nat):Int)<q) → e.tape q=t q) ∧
      silentSegment machine (cfg 93 a t) e
        ((2*k+y+6)+(len+1)+(v+3+(encode rest).length)) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let x := d+(y : Int)+2+(len : Int)+1
  let selected := clearAt d t
  have hunit := marker_unit_to12 t a k y z ws window
  have hunit' : silentSegment machine (cfg 93 a t) (cfg 12 (d+(y : Int)+2) selected) (2*k+y+6) := by
    simpa only [d,selected] using hunit
  have hword : Holds selected (d+(y : Int)+2) (List.replicate len true ++ [false]) := by
    apply holds_transport t selected _ _ word
    intro q hq _
    simp [selected,clearAt,show q≠d by dsimp [d] at hq; omega]
  have hscan := scan12 len (d+(y : Int)+2) selected hword
  have hscan' : silentSegment machine (cfg 12 (d+(y : Int)+2) selected) (cfg 14 x selected) (len+1) := by
    simpa only [x] using hscan
  have hbank : Holds selected x (encode (v::rest) ++ [false]) := by
    apply holds_transport t selected _ _ bank
    intro q hq _
    simp [selected,clearAt,show q≠d by dsimp [x,d] at hq; omega]
  obtain ⟨e,hs,hh,hebank,hframe,hinc⟩ := encoded_increment v rest x selected hbank
  have hframe' : ∀ q, q≠d → (q<x ∨ x+(((v+1)+(encode rest).length : Nat):Int)<q) → e.tape q=t q := by
    intro q hq hf
    calc
      e.tape q=selected q := hframe q hf
      _=t q := by simp [selected,clearAt,hq]
  have hfirst := segAdd machine _ _ _ (2*k+y+6) (len+1) hunit' hscan'
  have hall := segAdd machine _ _ _ _ (v+3+(encode rest).length) hfirst hinc
  exact ⟨e,hs,hh,hebank,(fun q hq => hframe q (Or.inl hq)),hframe',hall⟩

/-- Retain the earlier variable-selector increment interface. -/
theorem unit_selector_bank_increment (t : Int → Bool) (a : Int) (k y z len v : Nat)
    (ws rest : List Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ 1::y::z::ws)))
    (word : Holds t (a+((2*k : Nat):Int)+4+(y : Int)+2) (List.replicate len true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+4+(y : Int)+2+(len : Int)+1)
      (encode (v::rest) ++ [false])) :
    let d := a+((2*k : Nat):Int)+4
    let x := d+(y : Int)+2+(len : Int)+1
    ∃ e : Config 284, e.state=23 ∧ e.head=x+(((v+1)+(encode rest).length : Nat):Int) ∧
      Holds e.tape x (encode ((v+1)::rest)) ∧
      (∀ q, q≠d → (q<x ∨ x+(((v+1)+(encode rest).length : Nat):Int)<q) → e.tape q=t q) ∧
      silentSegment machine (cfg 93 a t) e
        ((2*k+y+6)+(len+1)+(v+3+(encode rest).length)) := by
  obtain ⟨e,hs,hh,hbank,_hleft,hframe,hseg⟩ :=
    unit_selector_bank_increment_with_control t a k y z len v ws rest window word bank
  exact ⟨e,hs,hh,hbank,hframe,hseg⟩

#print axioms unit_selector_bank_increment
end Shared.Beeping.NPcoNP.NativeUnitSelectorBankIncrement
