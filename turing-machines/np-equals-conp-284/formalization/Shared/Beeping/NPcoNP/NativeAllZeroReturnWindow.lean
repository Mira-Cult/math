import Shared.Beeping.NPcoNP.NativeAllZeroActualBit

/-! The selector window after the actual long marker-absent return.
All statements require a supplied prepared layout; no blank-start invariant
or register-graph refinement is asserted. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroReturnWindow
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentDispatch
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentReturn
open Shared.Beeping.NPcoNP.NativeAllZeroActualBit
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000
attribute [local irreducible] machine

/-- The carry output sets the marker immediately left of its clear run. -/
theorem return_left_marker (d : Int) (r : Nat) (t : Int → Bool) :
    outTape d r t (d-4)=true := by
  unfold outTape
  rw [put_other _ _ _ _ (by omega)]
  change (if d+3≤d-4 ∧ d-4<d+2+(r : Int) then false else scanTape d t (d-4))=true
  rw [if_neg (by omega)]
  change put (carryTape d t) (d+2) false (d-4)=true
  rw [put_other _ _ _ _ (by omega)]
  change put (cleared t (d-1) 3) ((d-1)-((3 : Nat):Int)) true (d-4)=true
  simp [put,show d-4=(d-1)-((3 : Nat):Int) by omega]

def preservedPrefix : List Bool := false :: (encode (List.replicate 11 0) ++ [true])

theorem initial_window_split :
    markerWindow (List.replicate 13 0 ++ [0]) =
      [false,true] ++ preservedPrefix ++ [false,true] := by decide

theorem next_window_split (r : Nat) :
    markerWindow (List.replicate 11 0 ++ [1,0,r+2]) =
      preservedPrefix ++ [true,false,true,false] ++ List.replicate (r+3) true := by
  apply List.append_cancel_right (bs := [false])
  have h := markerWindow_append_zero (List.replicate 11 0 ++ [1,0,r+2])
  simpa [preservedPrefix,encode_append,encode,block,List.append_assoc] using h

/-- The exact long-return tape has the next marked selector window, provided
the protected prefix still agrees with the original prepared window. -/
theorem long_return_window (a : Int) (r v : Nat) (rest : List Nat)
    (initial t1 : Int → Bool)
    (window : Holds initial a (markerWindow (List.replicate 13 0 ++ [0])))
    (frame : ∀ q, q<a+26 →
      fillRange (setAt (a+28) (outTape (a+30) (r+3) (selectorOutput a r v rest t1)))
        (a+30) (a+34+(r : Int)) q=initial q) :
    let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
    let output := fillRange (setAt (a+28) final) (a+30) (a+34+(r : Int))
    Holds output (a+2) (markerWindow (List.replicate 11 0 ++ [1,0,r+2])) ∧
      output (a+1)=true := by
  dsimp only
  let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
  let output := fillRange (setAt (a+28) final) (a+30) (a+34+(r : Int))
  have hprefix0 : Holds initial (a+2) preservedPrefix := by
    have hw := window
    rw [initial_window_split] at hw
    have htail := holds_append_tail initial a [false,true] (preservedPrefix ++ [false,true]) hw
    have hp : a+(([false,true].length : Nat):Int)=a+2 := by norm_num
    rw [hp] at htail
    exact holds_prefix_word initial (a+2) preservedPrefix [false,true] htail
  have hprefixlen : preservedPrefix.length=24 := by decide
  have hprefix : Holds output (a+2) preservedPrefix := by
    apply holds_transport initial output _ _ hprefix0
    intro q _ hq
    rw [hprefixlen] at hq
    symm
    exact frame q (by omega)
  have hleft : output (a+1)=true := by
    have hf : output (a+1)=initial (a+1) := frame (a+1) (by omega)
    rw [hf]
    have h := holds_get initial a _ window 1 (by decide)
    have hb : (markerWindow (List.replicate 13 0 ++ [0]))[1]=true := by decide
    rw [hb] at h
    simpa using h
  have h26 : output (a+26)=true := by
    have hout : output (a+26)=final (a+26) := by simp [output,fillRange,setAt]
    rw [hout]
    have hp : a+30-4=a+26 := by omega
    simpa only [final,hp] using return_left_marker (a+30) (r+3) (selectorOutput a r v rest t1)
  have h27 : output (a+27)=false := by
    have hout : output (a+27)=final (a+27) := by simp [output,fillRange,setAt]
    rw [hout]
    have hp : a+30-3=a+27 := by omega
    simpa only [final,hp] using return_clears_after_marker (a+30) (r+3) (selectorOutput a r v rest t1)
  have h28 : output (a+28)=true := by simp [output,fillRange,setAt]
  have h29 : output (a+29)=false := by
    have hout : output (a+29)=final (a+29) := by simp [output,fillRange,setAt]
    rw [hout]
    apply return_carry_gap
    all_goals omega
  have hrun : Holds output (a+30) (List.replicate (r+3) true) := by
    apply holds_of_get
    intro i hi
    have hr : i<r+3 := by simpa using hi
    have hp : a+30≤a+30+(i : Int) ∧ a+30+(i : Int)<a+34+(r : Int) := by omega
    simp [output,fillRange,hp]
  have htail : Holds output (a+26) ([true,false,true,false] ++ List.replicate (r+3) true) := by
    simp only [List.cons_append,List.nil_append,Holds]
    refine ⟨h26,?_,?_,?_,?_⟩
    · simpa only [show a+26+1=a+27 by omega] using h27
    · simpa only [show a+26+1+1=a+28 by omega] using h28
    · simpa only [show a+26+1+1+1=a+29 by omega] using h29
    · simpa only [show a+26+1+1+1+1=a+30 by omega] using hrun
  have hfull := holds_append_intro output (a+2) preservedPrefix
    ([true,false,true,false] ++ List.replicate (r+3) true) hprefix (by
      have hp : a+2+(preservedPrefix.length : Int)=a+26 := by rw [hprefixlen]; norm_num; omega
      rw [hp]
      exact htail)
  constructor
  · rw [next_window_split]
    simpa [List.append_assoc] using hfull
  · exact hleft

/-- The new window and its left marker send state 83 to state 93 at the
new anchor in exactly `r+32` silent, tape-preserving steps. -/
theorem long_return_window_to93 (a : Int) (r : Nat) (t : Int → Bool)
    (window : Holds t (a+2) (markerWindow (List.replicate 11 0 ++ [1,0,r+2])))
    (marker : t (a+1)=true) :
    silentSegment machine (cfg 83 (a+32+(r : Int)) t) (cfg 93 (a+2) t) (r+32) := by
  let xs := List.replicate 11 0 ++ [1,0,r+2]
  have hlen : (encode xs).length=r+31 := by
    simp [xs,encode,block_length]
    omega
  have h := marker_window_to93 t (a+2) xs (by simp [xs]) window (by
    have hp : a+2-1=a+1 := by omega
    simpa only [hp] using marker)
  rw [hlen] at h
  have hp : a+2+((r+31 : Nat):Int)-1=a+32+(r : Int) := by push_cast; omega
  have hc : r+31+1=r+32 := by omega
  simpa only [hp,hc] using h

/-- The supplied marker-absent cycle reaches the next state-93 boundary
with its exact window, extended bank, and protected left tape. -/
theorem padded_absent_next93 (a : Int) (r v : Nat) (rest : List Nat)
    (suffix : List Bool) (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (left0 : t (a-2)=false) (earlier : t (a-1)=true)
    (absent : t (a-3)=false)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int))
      ((encode (v::rest) ++ [false,false,false]) ++ ([false,false] ++ suffix))) :
    ∃ mid : Config 284, mid.state=23 ∧
      let t1 := setAt (a+29) (setAt (a+30) mid.tape)
      let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
      let output := fillRange (setAt (a+28) final) (a+30) (a+34+(r : Int))
      silentSegment machine (cfg 93 a t) (cfg 93 (a+2) output)
        ((((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28+(r+8))+(r+32)) ∧
      Holds output (a+2) (markerWindow (List.replicate 11 0 ++ [1,0,r+2])) ∧
      output (a+1)=true ∧
      Holds output (a+36+(r : Int))
        ((encode ((v::rest) ++ [0]) ++ [false,false,false]) ++ suffix) ∧
      (∀ q, q<a+26 → output q=t q) := by
  obtain ⟨mid,hs,hseg,hbank,hleft⟩ :=
    padded_absent_long_return a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  let t1 := setAt (a+29) (setAt (a+30) mid.tape)
  let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
  let output := fillRange (setAt (a+28) final) (a+30) (a+34+(r : Int))
  obtain ⟨hwindow,hmarker⟩ := long_return_window a r v rest t t1 window hleft
  have hnext := long_return_window_to93 a r output hwindow hmarker
  have hall := segAdd machine _ _ _ _ (r+32) hseg hnext
  exact ⟨mid,hs,hall,hwindow,hmarker,hbank,hleft⟩

#print axioms padded_absent_next93
#print axioms long_return_window_to93
#print axioms long_return_window
#print axioms return_left_marker
#print axioms initial_window_split
#print axioms next_window_split
end Shared.Beeping.NPcoNP.NativeAllZeroReturnWindow
