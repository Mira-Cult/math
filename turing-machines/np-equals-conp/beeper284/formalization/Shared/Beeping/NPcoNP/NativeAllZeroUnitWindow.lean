import Shared.Beeping.NPcoNP.NativeAllZeroUnitScan
import Shared.Beeping.NPcoNP.NativeAllZeroReturnWindow

/-! The selector layout and dispatch after the supplied unit scan. This is a
finite prepared-layout result, not a blank-start or graph simulation theorem. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroUnitWindow
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroNearCarry
open Shared.Beeping.NPcoNP.NativeAllZeroUnitScan
open Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping.NPcoNP.NativeAllZeroReturnWindow
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
attribute [local irreducible] machine

theorem unit_scan_window_split (r : Nat) :
    markerWindow (List.replicate 12 0 ++ [3,r+2]) =
      ([false,true] ++ preservedPrefix) ++ [true,true,true,false] ++ List.replicate (r+3) true := by
  apply List.append_cancel_right (bs := [false])
  have h := markerWindow_append_zero (List.replicate 12 0 ++ [3,r+2])
  simpa [preservedPrefix,encode_append,encode,block,List.append_assoc] using h

/-- The scan merges the former unit block with its neighbor. Accounting for
the two preserved cells on the left produces fourteen selector blocks. -/
theorem unit_scan_window (a : Int) (r : Nat) (initial t : Int → Bool)
    (window : Holds initial a zeroWord) (h26 : t (a+26)=true)
    (h29 : t (a+29)=false)
    (frame : ∀ q, q<a+26 →
      fillRange (setAt (a+28) (carryOutput a r t)) (a+30) (a+34+(r : Int)) q=initial q) :
    let output := fillRange (setAt (a+28) (carryOutput a r t)) (a+30) (a+34+(r : Int))
    Holds output a (markerWindow (List.replicate 12 0 ++ [3,r+2])) := by
  let output := fillRange (setAt (a+28) (carryOutput a r t)) (a+30) (a+34+(r : Int))
  let pref := [false,true] ++ preservedPrefix
  have hprefix0 : Holds initial a pref := by
    have hw := window
    change Holds initial a (markerWindow (List.replicate 13 0 ++ [0])) at hw
    rw [initial_window_split] at hw
    exact holds_prefix_word initial a pref [false,true] (by simpa [pref,List.append_assoc] using hw)
  have hprefixlen : pref.length=26 := by decide
  have hprefix : Holds output a pref := by
    apply holds_transport initial output _ _ hprefix0
    intro q _ hq
    rw [hprefixlen] at hq
    symm
    exact frame q (by omega)
  have hz26 : output (a+26)=true := by
    have hf : carryOutput a r t (a+26)=t (a+26) := near_carry_frame a r t (a+26) (Or.inl (by omega))
    simpa [output,fillRange,setAt,hf] using h26
  have hz27 : output (a+27)=true := by
    have hc : carryOutput a r t (a+27)=true := by simp [carryOutput,put,clearRange]
    simpa [output,fillRange,setAt,hc] using hc
  have hz28 : output (a+28)=true := by simp [output,fillRange,setAt]
  have hz29 : output (a+29)=false := by
    have hc : carryOutput a r t (a+29)=false := by
      simp [carryOutput,put,clearRange,h29]
      omega
    simpa [output,fillRange,setAt,hc] using hc
  have hrun : Holds output (a+30) (List.replicate (r+3) true) := by
    apply holds_of_get
    intro i hi
    have hr : i<r+3 := by simpa using hi
    have hp : a+30≤a+30+(i : Int) ∧ a+30+(i : Int)<a+34+(r : Int) := by omega
    simp [output,fillRange,hp]
  have htail : Holds output (a+26) ([true,true,true,false] ++ List.replicate (r+3) true) := by
    simp only [List.cons_append,List.nil_append,Holds]
    refine ⟨hz26,?_,?_,?_,?_⟩
    · simpa only [show a+26+1=a+27 by omega] using hz27
    · simpa only [show a+26+1+1=a+28 by omega] using hz28
    · simpa only [show a+26+1+1+1=a+29 by omega] using hz29
    · simpa only [show a+26+1+1+1+1=a+30 by omega] using hrun
  have hfull := holds_append_intro output a pref
    ([true,true,true,false] ++ List.replicate (r+3) true) hprefix (by
      have hp : a+(pref.length : Int)=a+26 := by rw [hprefixlen]; norm_num
      rw [hp]
      exact htail)
  change Holds output a _
  rw [unit_scan_window_split]
  simpa [pref,List.append_assoc] using hfull

/-- The resulting fourteen-block window returns to the original state-93
anchor with no tape changes or events. -/
theorem unit_scan_window_to93 (a : Int) (r : Nat) (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 12 0 ++ [3,r+2])))
    (marker : t (a-1)=true) :
    silentSegment machine (cfg 83 (a+32+(r : Int)) t) (cfg 93 a t) (r+34) := by
  let xs := List.replicate 12 0 ++ [3,r+2]
  have hlen : (encode xs).length=r+33 := by
    simp [xs,encode,block_length]
    omega
  have h := marker_window_to93 t a xs (by simp [xs]) window marker
  rw [hlen] at h
  have hp : a+((r+33 : Nat):Int)-1=a+32+(r : Int) := by push_cast; omega
  have hc : r+33+1=r+34 := by omega
  simpa only [hp,hc] using h

/-- Starting from the supplied padded layout, the next state-93 boundary
has the explicit fourteen-block selector and updated bank. -/
theorem padded_absent_next93_after_unit (a : Int) (r v : Nat) (rest : List Nat)
    (suffix : List Bool) (t : Int → Bool)
    (window : Holds t a zeroWord)
    (left0 : t (a-2)=false) (earlier : t (a-1)=true)
    (absent : t (a-3)=false)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int))
      ((encode (v::rest) ++ [false,false,false]) ++ ([false,false] ++ suffix))) :
    ∃ (mid e : Config 284) (n : Nat), mid.state=23 ∧ e.state=23 ∧ 0<n ∧
      let output := fillRange (setAt (a+28) (carryOutput a r e.tape))
        (a+30) (a+34+(r : Int))
      silentSegment machine (cfg 93 a t) (cfg 93 a output) n ∧
      Holds output a (markerWindow (List.replicate 12 0 ++ [3,r+2])) ∧
      Holds output (a+36+(r : Int))
        ((encode ((v+1)::(rest ++ [0])) ++ [false,false]) ++ suffix) ∧
      (∀ q, q<a+26 → output q=t q) := by
  obtain ⟨mid,e,n,hs,he,hn,hseg,hbank,h26,h29,hframe⟩ :=
    padded_absent_unit_scan_with_control a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  let output := fillRange (setAt (a+28) (carryOutput a r e.tape)) (a+30) (a+34+(r : Int))
  have hwindow := unit_scan_window a r t e.tape window h26 h29 hframe
  have hmarker : output (a-1)=true := (hframe _ (by omega)).trans earlier
  have hnext := unit_scan_window_to93 a r output hwindow hmarker
  have hall := segAdd machine _ _ _ n (r+34) hseg hnext
  exact ⟨mid,e,n+(r+34),hs,he,by omega,hall,hwindow,hbank,hframe⟩

#print axioms unit_scan_window_split
#print axioms unit_scan_window
#print axioms unit_scan_window_to93
#print axioms padded_absent_next93_after_unit
end Shared.Beeping.NPcoNP.NativeAllZeroUnitWindow
