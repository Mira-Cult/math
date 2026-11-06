import Shared.Beeping.NPcoNP.NativeVariableFilledWindow
import Shared.Beeping.NPcoNP.NativeTerminalUnitSelector
import Shared.Beeping.NPcoNP.NativeVariableMarkerReturn

/-! A variable-length positive selector, fill and literal return to state 93. -/
namespace Shared.Beeping.NPcoNP.NativeVariablePositiveRoundtrip
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeVariableFilledWindow
open Shared.Beeping.NPcoNP.NativeVariableMarkerReturn
open Shared.Beeping.NPcoNP.NativeZeroSelectorScan
open Shared.Beeping.NPcoNP.NativeTerminalUnitSelector
open Shared.Beeping.NPcoNP.NativeVariableWindowWords
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

theorem unit_extends_zero_window (k : Nat) :
    markerWindow (List.replicate k 0 ++ [1]) =
      markerWindow (List.replicate k 0 ++ [0]) ++ [true] := by
  rw [terminal_window,zero_window_prefix]
  simp [List.append_assoc]

/-- For any supplied shortened positive selector with at most eleven leading
zero blocks, a finite corridor returns to the same state-93 anchor, with an
exact output window and frame. -/
theorem variable_positive_roundtrip (t : Int → Bool) (a : Int) (k r : Nat)
    (hk : k≤11)
    (hpre : Holds t a (markerWindow (List.replicate k 0 ++ [0])))
    (blank : ∀ q, q<a-2 → t q=false)
    (left0 : t (a-2)=false) (left1 : t (a-1)=true)
    (mark : t (a+((2*k : Nat):Int)+2)=true)
    (next : t (a+((2*k : Nat):Int)+3)=true)
    (h0 : t (a+((2*k : Nat):Int)+4)=false)
    (h1 : t (a+((2*k : Nat):Int)+5)=false)
    (zeros : ∀ i : Nat, i<r+2 → t (a+((2*k : Nat):Int)+6+(i : Int))=false)
    (stop : t (a+((2*k : Nat):Int)+6+((r+2 : Nat):Int))=true) :
    let d := a+((2*k : Nat):Int)+4
    let out := fillRange (setAt d t) (d+2) (d+2+((r+2 : Nat):Int))
    silentSegment machine (cfg 93 a t) (cfg 93 a out) (2*k+2*r+44) ∧
      Holds out (a-2) (markerWindow (List.replicate (k+1) 0 ++ [3,r])) ∧
      (∀ q, q<d ∨ d+2+((r+2 : Nat):Int)≤q → out q=t q) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let out := fillRange (setAt d t) (d+2) (d+2+((r+2 : Nat):Int))
  have hlen0 : (markerWindow (List.replicate k 0 ++ [0])).length=2*k+2 := by
    simp [encode_append,encode,zeros_length,block_length]
  have hmarkword : Holds t (a+((markerWindow (List.replicate k 0 ++ [0])).length : Int)) [true] := by
    rw [hlen0]
    have hp : a+((2*k+2 : Nat):Int)=a+((2*k : Nat):Int)+2 := by push_cast; omega
    rw [hp]
    simpa [Holds] using mark
  have hunit : Holds t a (markerWindow (List.replicate k 0 ++ [1])) := by
    rw [unit_extends_zero_window]
    exact holds_append_intro t a (markerWindow (List.replicate k 0 ++ [0])) [true] hpre hmarkword
  have hfirst := terminal_unit_fill_return t a k (r+2) (by omega) hunit next h0 h1 zeros stop
  obtain ⟨hwindow,hframe⟩ := variable_filled_window t a k r true hpre left0 left1 mark next h1
  have hw : Holds out (a-2) (markerWindow (List.replicate (k+1) 0 ++ [3,r])) := by
    simpa only [↓reduceIte,d,out] using hwindow
  have hf : ∀ q, q<d ∨ d+2+((r+2 : Nat):Int)≤q → out q=t q := by
    simpa only [d,out] using hframe
  let xs := List.replicate (k+1) 0 ++ [3,r]
  have hcount : xs.length=k+3 := by simp [xs]
  have hlen : (encode xs).length=2*k+r+9 := by
    simp [xs,encode_append,encode,zeros_length,block_length]
    omega
  have hblank : ∀ q, q<a-2 → out q=false := by
    intro q hq
    exact (hf q (Or.inl (by dsimp [d]; omega))).trans (blank q hq)
  have hleft0 : out (a-2)=false := (hf _ (Or.inl (by dsimp [d]; omega))).trans left0
  have hleft1 : out (a-1)=true := (hf _ (Or.inl (by dsimp [d]; omega))).trans left1
  have hreturn := variable_marker_return out (a-2) xs (by rw [hcount]; omega) hw
    hblank (by simpa using hleft0) (by simpa only [show a-2+1=a-1 by omega] using hleft1)
  have hfirst' : silentSegment machine (cfg 93 a t) (cfg 83 (d+((r+2 : Nat):Int)) out) (2*k+r+10) := by
    have hc : 2*k+(r+2)+8=2*k+r+10 := by omega
    simpa only [d,out,hc] using hfirst
  have hreturn' : silentSegment machine (cfg 83 (d+((r+2 : Nat):Int)) out) (cfg 93 a out) (r+34) := by
    rw [hlen,hcount] at hreturn
    have hh : a-2+((2*k+r+9 : Nat):Int)-1=d+((r+2 : Nat):Int) := by dsimp [d]; push_cast; omega
    have he : a-2+2=a := by omega
    have hc : 2*k+r+9+2*(14-(k+3))+3=r+34 := by omega
    simpa only [hh,he,hc] using hreturn
  have hall := segAdd machine _ _ _ (2*k+r+10) (r+34) hfirst' hreturn'
  have hc : 2*k+r+10+(r+34)=2*k+2*r+44 := by omega
  exact ⟨by simpa only [hc] using hall,hw,hf⟩

#print axioms variable_positive_roundtrip
end Shared.Beeping.NPcoNP.NativeVariablePositiveRoundtrip
