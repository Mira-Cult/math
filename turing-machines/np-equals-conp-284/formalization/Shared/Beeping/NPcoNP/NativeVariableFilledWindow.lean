import Shared.Beeping.NPcoNP.NativeVariableWindowWords
import Shared.Beeping.NPcoNP.NativeZeroSelectorScan

/-! Selector windows created by variable-length zero and positive scans. -/
namespace Shared.Beeping.NPcoNP.NativeVariableFilledWindow
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeVariableWindowWords
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- Both physical branches preserve the prefix and fill the supplied corridor.
The bit immediately before the scan selects the resulting unit or positive
window; all cells outside the scan are framed. -/
theorem variable_filled_window (t : Int → Bool) (a : Int) (k r : Nat) (branch : Bool)
    (hpre : Holds t a (markerWindow (List.replicate k 0 ++ [0])))
    (left0 : t (a-2)=false) (left1 : t (a-1)=true)
    (mark : t (a+((2*k : Nat):Int)+2)=true)
    (next : t (a+((2*k : Nat):Int)+3)=branch)
    (zero : t (a+((2*k : Nat):Int)+5)=false) :
    let d := a+((2*k : Nat):Int)+4
    let out := fillRange (setAt d t) (d+2) (d+2+((r+2 : Nat):Int))
    Holds out (a-2) (markerWindow (List.replicate (k+1) 0 ++
      (if branch then [3,r] else [1,0,r]))) ∧
      (∀ q, q<d ∨ d+2+((r+2 : Nat):Int)≤q → out q=t q) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let stop := d+2+((r+2 : Nat):Int)
  let out := fillRange (setAt d t) (d+2) stop
  have hframe : ∀ q, q<d ∨ stop≤q → out q=t q := by
    intro q hq
    have hn : q≠d := by dsimp [stop] at hq; omega
    have hr : ¬(d+2≤q ∧ q<stop) := by omega
    simp [out,fillRange,setAt,hn,hr]
  have hlen : (markerWindow (List.replicate k 0 ++ [0])).length=2*k+2 := by
    simp [encode_append,encode,zeros_length,block_length]
  have hpref : Holds out a (markerWindow (List.replicate k 0 ++ [0])) := by
    apply holds_transport t out _ _ hpre
    intro q _ hq
    rw [hlen] at hq
    exact (hframe q (Or.inl (by dsimp [d]; push_cast at hq; omega))).symm
  have hpair : Holds out (a-2) [false,true] := by
    simp only [Holds]
    exact ⟨(hframe _ (Or.inl (by dsimp [d]; omega))).trans left0,
      by simpa only [show a-2+1=a-1 by omega] using
        (hframe _ (Or.inl (by dsimp [d]; omega))).trans left1,trivial⟩
  have hprefix := holds_append_intro out (a-2) [false,true]
    (markerWindow (List.replicate k 0 ++ [0])) hpair (by
      have hp : a-2+(([false,true].length : Nat):Int)=a := by norm_num
      rw [hp]
      exact hpref)
  have hm : out (d-2)=true := by
    have hp : d-2=a+((2*k : Nat):Int)+2 := by dsimp [d]; omega
    rw [hp,hframe _ (Or.inl (by dsimp [d]; omega))]
    exact mark
  have hn : out (d-1)=branch := by
    have hp : d-1=a+((2*k : Nat):Int)+3 := by dsimp [d]; omega
    rw [hp,hframe _ (Or.inl (by dsimp [d]; omega))]
    exact next
  have hd : out d=true := by simp [out,fillRange,setAt,stop]
  have hz : out (d+1)=false := by
    have hp : d+1=a+((2*k : Nat):Int)+5 := by dsimp [d]; omega
    have ht : t (d+1)=false := by simpa only [hp] using zero
    simpa [out,fillRange,setAt,stop] using ht
  have hrun : Holds out (d+2) (List.replicate (r+1) true) := by
    apply holds_of_get
    intro i hi
    have hi' : i<r+1 := by simpa using hi
    have hr : d+2≤d+2+(i : Int) ∧ d+2+(i : Int)<stop := by dsimp [stop]; omega
    simp only [List.getElem_replicate]
    simp [out,fillRange,hr]
  have htail : Holds out (d-2) ([true,branch,true,false] ++ List.replicate (r+1) true) := by
    simp only [List.cons_append,List.nil_append,Holds]
    refine ⟨hm,?_,?_,?_,?_⟩
    · simpa only [show d-2+1=d-1 by omega] using hn
    · simpa only [show d-2+1+1=d by omega] using hd
    · simpa only [show d-2+1+1+1=d+1 by omega] using hz
    · simpa only [show d-2+1+1+1+1=d+2 by omega] using hrun
  have hfull := holds_append_intro out (a-2) ([false,true] ++ markerWindow (List.replicate k 0 ++ [0]))
    ([true,branch,true,false] ++ List.replicate (r+1) true) hprefix (by
      have hl : ([false,true] ++ markerWindow (List.replicate k 0 ++ [0])).length=2*k+4 := by
        simp [hlen]
      have hp : a-2+((([false,true] ++ markerWindow (List.replicate k 0 ++ [0])).length : Nat):Int)=d-2 := by
        rw [hl]; dsimp [d]; push_cast; omega
      rw [hp]
      exact htail)
  constructor
  · cases branch with
    | false => simpa [variable_unit_window_word,List.append_assoc,out,d,stop] using hfull
    | true => simpa [variable_positive_window_word,List.append_assoc,out,d,stop] using hfull
  · exact hframe

#print axioms variable_filled_window
end Shared.Beeping.NPcoNP.NativeVariableFilledWindow
