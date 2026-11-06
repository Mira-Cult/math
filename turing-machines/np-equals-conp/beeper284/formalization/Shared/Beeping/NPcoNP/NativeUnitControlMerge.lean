import Shared.Beeping.NPcoNP.NativeUnitWindowTerminalNet
import Shared.Beeping.NPcoNP.NativeIncBank
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14

/-! Word-level transition at a unit/terminal compound return. -/
namespace Shared.Beeping.NPcoNP.NativeUnitControlMerge
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnit14
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- Writing one tape cell transforms the corresponding finite word by the
same list update. No condition on cells outside the word is required. -/
theorem holds_setAt (t : Int → Bool) (a : Int) (xs : List Bool) (i : Nat)
    (hw : Holds t a xs) :
    Holds (setAt (a+(i : Int)) t) a (xs.set i true) := by
  induction xs generalizing a i with
  | nil => simp [Holds]
  | cons x xs ih =>
    cases i with
    | zero =>
      change t a=x ∧ Holds t (a+1) xs at hw
      simp only [List.set_cons_zero,Holds]
      constructor
      · simp [setAt]
      · simp only [Nat.cast_zero,add_zero]
        apply holds_transport t (setAt a t) (a+1) xs hw.2
        intro q hq _
        simp [setAt,show q≠a by omega]
    | succ i =>
      change t a=x ∧ Holds t (a+1) xs at hw
      simp only [List.set_cons_succ,Holds]
      constructor
      · have hn : a≠a+((Nat.succ i : Nat):Int) := by push_cast; omega
        change (if a=a+((Nat.succ i : Nat):Int) then true else t a)=x
        rw [if_neg hn]
        exact hw.1
      · have hh := ih (a+1) i hw.2
        have he : a+((Nat.succ i : Nat):Int)=a+1+(i : Int) := by push_cast; omega
        simpa only [he] using hh

/-- The selected separator is strictly inside the old marked window. -/
theorem merge_index_lt (k z : Nat) (zs : List Nat) :
    2*k+3 < (markerWindow (List.replicate k 0 ++ 1::0::z::zs)).length := by
  rw [markerWindow_length,encode_append]
  simp [zeros_length,encode,block_length]

/-- Setting the unit/zero separator and adjoining an earlier zero block
merges those two blocks into one block of value three. -/
theorem merged_window_word (k z : Nat) (zs : List Nat) :
    markerWindow (List.replicate (k+1) 0 ++ 3::z::zs) =
      [false,true] ++ (markerWindow (List.replicate k 0 ++ 1::0::z::zs)).set (2*k+3) true := by
  let old := List.replicate k 0 ++ 1::0::z::zs
  let new := List.replicate (k+1) 0 ++ 3::z::zs
  have hbound : 2*k+3 < (markerWindow old).length := merge_index_lt k z zs
  apply List.append_cancel_right (bs := [false])
  have hs : (markerWindow old).set (2*k+3) true ++ [false] =
      (false::encode old).set (2*k+3) true := by
    rw [← List.set_append_left (2*k+3) true hbound, markerWindow_append_zero]
  rw [List.append_assoc,hs,markerWindow_append_zero]
  simp [old,encode_append,encode,block,zeros_length,List.replicate_succ,
    List.set_append_right,List.append_assoc]

/-- The shifted window is two cells longer, so moving its left edge left
by two keeps its right-hand marker fixed. -/
theorem merged_window_length (k z : Nat) (zs : List Nat) :
    (encode (List.replicate (k+1) 0 ++ 3::z::zs)).length =
      (encode (List.replicate k 0 ++ 1::0::z::zs)).length+2 := by
  have hh := congrArg List.length (merged_window_word k z zs)
  simp only [markerWindow_length,List.length_append,List.length_cons,List.length_nil,List.length_set] at hh
  omega

#print axioms merged_window_length

/-- A single separator write, with an unchanged left frame, establishes the
new marked control window and its bounding markers. -/
theorem merge_control_window (t out : Int → Bool) (a : Int) (k z : Nat) (zs : List Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ 1::0::z::zs)))
    (left0 : t (a-2)=false) (left1 : t (a-1)=true) (before : t (a-3)=true)
    (right : t (a+((encode (List.replicate k 0 ++ 1::0::z::zs)).length : Int))=true)
    (written : out (a+((2*k+3 : Nat):Int))=true)
    (frame : ∀ q, q≤a+((encode (List.replicate k 0 ++ 1::0::z::zs)).length : Int) →
      q≠a+((2*k+3 : Nat):Int) → out q=t q) :
    Holds out (a-2) (markerWindow (List.replicate (k+1) 0 ++ 3::z::zs)) ∧
      out (a-3)=true ∧
      out (a+((encode (List.replicate k 0 ++ 1::0::z::zs)).length : Int))=true := by
  let xs := List.replicate k 0 ++ 1::0::z::zs
  let edge := a+((encode xs).length : Int)
  let bit := a+((2*k+3 : Nat):Int)
  let patched := setAt bit t
  have hi : 2*k+3 < (markerWindow xs).length := merge_index_lt k z zs
  have hbit : bit<edge := by
    dsimp [bit,edge] at *
    rw [markerWindow_length] at hi
    omega
  have hw : Holds patched a ((markerWindow xs).set (2*k+3) true) := by
    exact holds_setAt t a (markerWindow xs) (2*k+3) window
  have hout : Holds out a ((markerWindow xs).set (2*k+3) true) := by
    apply holds_transport patched out a _ hw
    intro q _ hq
    by_cases he : q=bit
    · subst q
      change setAt bit t bit=out bit
      have hwbit : out bit=true := written
      simp only [setAt]
      exact hwbit.symm
    · have hh : q<edge := by
        have hlen : ((markerWindow xs).set (2*k+3) true).length=(encode xs).length := by
          simp [markerWindow_length]
        rw [hlen] at hq
        exact hq
      change setAt bit t q=out q
      rw [show setAt bit t q=t q by simp [setAt,he]]
      symm
      have hqedge : q≤a+((encode (List.replicate k 0 ++ 1::0::z::zs)).length : Int) := by
        change q≤edge
        omega
      exact frame q hqedge (by simpa [bit] using he)
  have hprefix : Holds out (a-2) [false,true] := by
    change out (a-2)=false ∧ out (a-2+1)=true ∧ True
    have h0 : out (a-2)=t (a-2) := frame (a-2) (by omega) (by dsimp [bit]; omega)
    have h1 : out (a-1)=t (a-1) := frame (a-1) (by omega) (by dsimp [bit]; omega)
    refine ⟨by rw [h0]; exact left0,?_,trivial⟩
    have he : a-2+1=a-1 := by omega
    rw [he,h1]
    exact left1
  have hw' : Holds out (a-2) ([false,true] ++ (markerWindow xs).set (2*k+3) true) := by
    apply holds_append_intro out (a-2) [false,true] _ hprefix
    simpa using hout
  have hbefore : out (a-3)=true := by
    rw [frame (a-3) (by omega) (by dsimp [bit]; omega)]
    exact before
  have hright : out edge=true := by
    have hq : edge≤a+((encode (List.replicate k 0 ++ 1::0::z::zs)).length : Int) := by
      change edge≤edge
      exact le_rfl
    have hne : edge≠a+((2*k+3 : Nat):Int) := by
      change edge≠bit
      omega
    rw [frame edge hq hne]
    exact right
  refine ⟨?_,hbefore,hright⟩
  rw [merged_window_word]
  exact hw'

#print axioms merge_control_window
#print axioms holds_setAt
#print axioms merged_window_word
end Shared.Beeping.NPcoNP.NativeUnitControlMerge
