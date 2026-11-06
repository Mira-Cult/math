import Shared.Beeping.NPcoNP.NativeAllZeroAbsentTo261
import Shared.Beeping.NPcoNP.NativeHalfState10Progress

/-! Progress from the state-261 boundary reached by the absent-marker branch.
The starting layout remains supplied and no graph refinement is asserted. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroAbsentReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
open Shared.Beeping.NPcoNP.NativeHalfState10Progress
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.NativeAllZeroAbsentTo261
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
attribute [local irreducible] machine

/-- The carry-and-return effect clears each of the three cells following
its left marker. -/
theorem return_carry_gap (d : Int) (r : Nat) (t : Int → Bool) (q : Int)
    (lo : d-4<q) (hi : q<d) : outTape d r t q=false := by
  unfold outTape clearRange scanTape carryTape result cleared put
  simp only
  have h0 : q ≠ d+1+(r : Int) := by omega
  have h1 : ¬ (d+3≤q ∧ q<d+2+(r : Int)) := by omega
  have h2 : q ≠ d+2 := by omega
  have h3 : q ≠ (d-1)-(3 : Int) := by omega
  have h4 : (d-1)-(3 : Int)<q ∧ q≤d-1 := by omega
  simp [h0,h1,h2,h3,h4]

/-- At the starting cell of the return, the outer return does not write. -/
theorem return_at_start (d : Int) (r : Nat) (t : Int → Bool) :
    outTape d r t d=t d := by
  unfold outTape clearRange scanTape carryTape result cleared put
  simp only
  have h0 : d ≠ d+1+(r : Int) := by omega
  have h1 : ¬ (d+3≤d ∧ d<d+2+(r : Int)) := by omega
  have h2 : d ≠ d+2 := by omega
  have h3 : d ≠ (d-1)-(3 : Int) := by omega
  have h4 : ¬ ((d-1)-(3 : Int)<d ∧ d≤d-1) := by omega
  simp [h0,h2,h3]

theorem return_marker (d : Int) (r : Nat) (t : Int → Bool) :
    outTape d r t (d+1+(r : Int))=true := by simp [outTape,put]

/-- The specified output tape supplies the zeros and right marker needed
for a positive finite silent return from state 261 to state 83. -/
theorem absent_return_to83 (a : Int) (r v : Nat) (rest : List Nat)
    (t1 : Int → Bool) :
    let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=83 ∧
      silentSegment machine (cfg 261 (a+28) final) e n := by
  let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
  have h0 : final (a+28)=false := by
    apply return_carry_gap
    all_goals omega
  have h1 : final (a+28+1)=false := by
    apply return_carry_gap
    all_goals omega
  have h2 : final (a+28+1+1)=false := by
    have hp : a+28+1+1=a+30 := by omega
    rw [hp]
    change outTape (a+30) (r+3) (selectorOutput a r v rest t1) (a+30)=false
    rw [return_at_start]
    unfold selectorOutput
    rw [spec_outside _ _ _ _ (Or.inl (by push_cast; omega))]
    simp [clearAt]
  have hm : final ((a+28+1+1)+((r+4 : Nat):Int))=true := by
    have hp : (a+28+1+1)+((r+4 : Nat):Int)=a+30+1+((r+3 : Nat):Int) := by push_cast; omega
    rw [hp]
    exact return_marker _ _ _
  exact dispatch261_zero_to83 (r+4) (a+28) final h0 h1 h2 hm

/-- The supplied padded cycle and absent-marker branch have a positive
finite silent continuation to state 83. The final state-83 tape is not
identified with a graph configuration by this theorem. -/
theorem padded_absent_return_to83 (a : Int) (r v : Nat) (rest : List Nat)
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
    ∃ (mid : Config 284) (n : Nat) (e : Config 284), mid.state=23 ∧ 0<n ∧ e.state=83 ∧
      let t1 := setAt (a+29) (setAt (a+30) mid.tape)
      let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
      silentSegment machine (cfg 93 a t) e
        (((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28+n) ∧
      Holds final (a+36+(r : Int))
        ((encode ((v::rest) ++ [0]) ++ [false,false,false]) ++ suffix) ∧
      (∀ q, q<a+26 → final q=t q) := by
  obtain ⟨mid,hs,hseg,_hwindow,hbank,hleft⟩ :=
    all_zero_padded_absent_to261 a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  let t1 := setAt (a+29) (setAt (a+30) mid.tape)
  let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
  obtain ⟨n,e,hn,he,hreturn⟩ := absent_return_to83 a r v rest t1
  have hall := segAdd machine _ _ _
    (((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
      ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
      ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28) n hseg hreturn
  exact ⟨mid,n,e,hs,hn,he,hall,hbank,hleft⟩

#print axioms padded_absent_return_to83
#print axioms return_carry_gap
#print axioms return_at_start
#print axioms return_marker
#print axioms absent_return_to83
end Shared.Beeping.NPcoNP.NativeAllZeroAbsentReturn
