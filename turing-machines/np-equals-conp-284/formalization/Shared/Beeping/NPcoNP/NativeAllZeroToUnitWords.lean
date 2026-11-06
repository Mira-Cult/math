import Shared.Beeping.NPcoNP.NativeAllZeroSelector
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
import Shared.Beeping.NPcoNP.NativeHalfTapeScan

/-! A parameterized all-zero fill followed by the next unit selector.
The hypotheses describe a supplied tape; they do not assert blank-start
reachability or a recurrent initialization invariant. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroToUnit
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroSelector
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
attribute [local irreducible] machine

def filled (a : Int) (r : Nat) (t : Int → Bool) : Int → Bool :=
  fillRange (setAt (a+30) t) (a+32) (a+34+(r : Int))

theorem filled_before (a : Int) (r : Nat) (t : Int → Bool) (q : Int)
    (h : q<a+30) : filled a r t q=t q := by
  change (if a+32≤q ∧ q<a+34+(r : Int) then true else
    if q=a+30 then true else t q)=t q
  rw [if_neg (by omega),if_neg (by omega)]

def controlPrefix : List Bool := false :: encode (List.replicate 11 0)

theorem prefix_length : controlPrefix.length=23 := by decide

/-- The next marked word, written in the order encountered on tape. -/
theorem unit_word (r : Nat) :
    markerWindow (List.replicate 11 0 ++ [1,0,r]) =
      controlPrefix ++ [true,true,false,true,false] ++ List.replicate (r+1) true := by
  apply List.append_cancel_right (bs := [false])
  rw [markerWindow_append_zero]
  simp [controlPrefix,encode_append,encode,block,List.replicate_succ,List.append_assoc]

theorem original_word : markerWindow (List.replicate 13 0 ++ [0]) =
    [false,true,false,true] ++ controlPrefix ++ [true] := by decide

/-- Filling the all-zero dispatch reconstructs the next unit window for
every finite run length. The next left marker is part of the old word. -/
theorem filled_window (a : Int) (r : Nat) (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h1 : t (a+31)=false) :
    Holds (filled a r t) (a+4) (markerWindow (List.replicate 11 0 ++ [1,0,r])) ∧
      filled a r t (a+3)=true := by
  have old := window
  rw [original_word] at old
  have htail := holds_append_tail t a [false,true,false,true]
    (controlPrefix ++ [true]) old
  have hpre : Holds t (a+4) controlPrefix := by
    apply holds_prefix_word t (a+4) controlPrefix [true]
    simpa using htail
  have hlast : t (a+27)=true := by
    have h := holds_get t a (markerWindow (List.replicate 13 0 ++ [0])) window 27 (by decide)
    have hb : (markerWindow (List.replicate 13 0 ++ [0]))[27]=true := by decide
    rw [hb] at h
    simpa using h
  have hleft : t (a+3)=true := by
    have h := holds_get t a (markerWindow (List.replicate 13 0 ++ [0])) window 3 (by decide)
    have hb : (markerWindow (List.replicate 13 0 ++ [0]))[3]=true := by decide
    rw [hb] at h
    simpa using h
  have hpre' : Holds (filled a r t) (a+4) controlPrefix := by
    apply holds_transport t (filled a r t) (a+4) controlPrefix hpre
    intro q hq hq'
    rw [prefix_length] at hq'
    exact (filled_before a r t q (by omega)).symm
  have c27 : filled a r t (a+27)=true := by
    rw [filled_before a r t (a+27) (by omega)]
    exact hlast
  have c28 : filled a r t (a+28)=true := by
    rw [filled_before a r t (a+28) (by omega)]
    exact marker
  have c29 : filled a r t (a+29)=false := by
    rw [filled_before a r t (a+29) (by omega)]
    exact nextZero
  have c30 : filled a r t (a+30)=true := by
    change (if a+32≤a+30 ∧ a+30<a+34+(r : Int) then true else
      if a+30=a+30 then true else t (a+30))=true
    rw [if_neg (by omega),if_pos rfl]
  have c31 : filled a r t (a+31)=false := by
    change (if a+32≤a+31 ∧ a+31<a+34+(r : Int) then true else
      if a+31=a+30 then true else t (a+31))=false
    rw [if_neg (by omega),if_neg (by omega)]
    exact h1
  have hcore : Holds (filled a r t) (a+27) [true,true,false,true,false] := by
    simpa only [Holds,Int.add_assoc,Int.reduceAdd] using
      (show filled a r t (a+27)=true ∧ filled a r t (a+28)=true ∧
        filled a r t (a+29)=false ∧ filled a r t (a+30)=true ∧
        filled a r t (a+31)=false ∧ True from ⟨c27,c28,c29,c30,c31,trivial⟩)
  have hrun : Holds (filled a r t) (a+32) (List.replicate (r+1) true) := by
    apply holds_of_get
    intro i hi
    have hi' : i<r+1 := by simpa only [List.length_replicate] using hi
    simp only [List.getElem_replicate]
    change (if a+32≤a+32+(i : Int) ∧ a+32+(i : Int)<a+34+(r : Int) then true else
      setAt (a+30) t (a+32+(i : Int)))=true
    rw [if_pos (by omega)]
  have hp : a+4+((controlPrefix.length : Nat) : Int)=a+27 := by
    rw [prefix_length]
    omega
  have hprefixcore := holds_append_intro (filled a r t) (a+4) controlPrefix
    [true,true,false,true,false] hpre' (by rw [hp]; exact hcore)
  have hp' : a+4+(((controlPrefix ++ [true,true,false,true,false]).length : Nat) : Int)=a+32 := by
    simp only [List.length_append,prefix_length,List.length_cons,List.length_nil,Nat.cast_add,Nat.cast_ofNat]
    omega
  have hwhole := holds_append_intro (filled a r t) (a+4)
    (controlPrefix ++ [true,true,false,true,false]) (List.replicate (r+1) true) hprefixcore
    (by rw [hp']; exact hrun)
  constructor
  · rw [unit_word]
    simpa [List.append_assoc] using hwhole
  · rw [filled_before a r t (a+3) (by omega)]
    exact hleft

#print axioms filled_window
end Shared.Beeping.NPcoNP.NativeAllZeroToUnit
