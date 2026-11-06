import Shared.Beeping.NPcoNP.NativeAllZeroNextReturn
import Shared.Beeping.NPcoNP.NativeHalfState27Scan
import Shared.Beeping.NPcoNP.NativeHalfScannerReturns
import Shared.Beeping.NPcoNP.NativeHalfMarkerExact

/-! Carry and return through the nearer zero pair of the supplied
marker-absent cycle. No blank-start or graph invariant is asserted. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroNearCarry
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeAllZeroNextReturn
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState27Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfState97Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfScannerReturns
open Shared.Beeping.NPcoNP.NativeHalfMarkerExact
open Shared.Beeping.NPcoNP.NativeIncBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000
attribute [local irreducible] machine

/-- State 1 writes the first zero, state 27 crosses the next pair, and
state 28 clears the following one-run before returning to state 83. -/
theorem near_carry_to83 (a : Int) (r : Nat) (t : Int → Bool)
    (h27 : t (a+27)=false) (h28 : t (a+28)=false) (h29 : t (a+29)=false)
    (run : Holds t (a+30) (List.replicate (r+5) true ++ [false])) :
    let t1 := put t (a+27) true
    let t2 := put t1 (a+30) false
    let output := put (clearRange t2 (a+31) (a+35+(r : Int))) (a+34+(r : Int)) true
    silentSegment machine (cfg 1 (a+27) t) (cfg 83 (a+26) output) (2*r+17) := by
  dsimp only
  let t1 := put t (a+27) true
  let t2 := put t1 (a+30) false
  let output := put (clearRange t2 (a+31) (a+35+(r : Int))) (a+34+(r : Int)) true
  have hw : Holds t (a+30) (true :: (List.replicate (r+4) true ++ [false])) := by
    have he : r+5=(r+4)+1 := by omega
    simpa only [he,List.replicate_succ,List.cons_append] using run
  have hone : t1 (a+30)=true := by
    change (if a+30=a+27 then true else t (a+30))=true
    rw [if_neg (by omega)]
    exact hw.1
  have hzeros : ∀ i : Nat, i<2 → t1 (a+28+(i : Int))=false := by
    intro i hi
    have hc : i=0 ∨ i=1 := by omega
    rcases hc with rfl | rfl
    · simp [t1,put,h28]
    · have hp : a+28+((1 : Nat):Int)=a+29 := by omega
      rw [hp]
      simp [t1,put,h29]
  have hfirst := oneSeg machine _ _ (NativeHalfState1Scan.step_zero (a+27) t h27)
  have hfirst' : silentSegment machine (cfg 1 (a+27) t) (cfg 27 (a+28) t1) 1 := by
    simpa only [show a+27+1=a+28 by omega,t1] using hfirst
  have h27scan := NativeHalfState27Scan.scan_to_one (a+28) t1 2 hzeros (by
    have hp : a+28+((2 : Nat):Int)=a+30 := by omega
    simpa only [hp] using hone)
  have hprefix : silentSegment machine (cfg 1 (a+27) t) (cfg 28 (a+31) t2) 4 := by
    have h := segAdd machine _ _ _ 1 3 hfirst' h27scan
    have hp : a+28+((2 : Nat):Int)+1=a+31 := by omega
    have hp2 : a+28+((2 : Nat):Int)=a+30 := by omega
    have hp3 : a+30+1=a+31 := by omega
    simpa only [hp,hp2,hp3,t1,t2,show 1+3=4 by decide] using h
  have htail : Holds t (a+31) (List.replicate (r+4) true ++ [false]) := by
    have hp : a+30+1=a+31 := by omega
    simpa only [hp] using hw.2
  have htail' : Holds t2 (a+31) (List.replicate (r+4) true ++ [false]) := by
    apply holds_transport t t2 _ _ htail
    intro q hq _
    symm
    change (if q=a+30 then false else if q=a+27 then true else t q)=t q
    rw [if_neg (by omega),if_neg (by omega)]
  have hsplit := split_ones (r+4) (a+31) t2 [false] htail'
  have hstop : t2 (a+31+((r+4 : Nat):Int))=false := by simpa [Holds] using hsplit.2
  have h28scan := scan28_return97 (r+4) (a+31) t2 (by omega) hsplit.1 hstop
  have hp : a+31+((r+4 : Nat):Int)=a+35+(r : Int) := by push_cast; omega
  have hh : a+31+((r+4 : Nat):Int)-2=a+33+(r : Int) := by push_cast; omega
  have hm : a+31+((r+4 : Nat):Int)-1=a+34+(r : Int) := by push_cast; omega
  have hc : r+4+2=r+6 := by omega
  rw [hh,hm,hp,hc] at h28scan
  have hmark : output (a+27)=true := by
    simp [output,put,clearRange,t2,t1]
  have hcorr : ∀ q, a+27<q → q≤a+33+(r : Int) → output q=false := by
    intro q hq hq'
    by_cases hlarge : a+31≤q
    · have hrange : a+31≤q ∧ q<a+35+(r : Int) := by omega
      have hn : q≠a+34+(r : Int) := by omega
      simp [output,put,hn,clearRange,hrange]
    · have hcases : q=a+28 ∨ q=a+29 ∨ q=a+30 := by omega
      rcases hcases with rfl | rfl | rfl
      · simp [output,put,clearRange,t2,t1,h28]; omega
      · simp [output,put,clearRange,t2,t1,h29]; omega
      · simp [output,put,clearRange,t2,t1]; omega
  have h97 := scan97_corridor (r+6) (a+33+(r : Int)) (a+27) output
    (by push_cast; omega) hmark hcorr
  have hprefix' := segAdd machine _ _ _ 4 (r+6) hprefix h28scan
  have hall := segAdd machine _ _ _ (4+(r+6)) ((r+6)+1) hprefix' h97
  have hp' : a+27-1=a+26 := by omega
  have hcost : 4+(r+6)+((r+6)+1)=2*r+17 := by omega
  simpa only [hp',hcost] using hall

/-- The carry and return preserve the tape outside their written interval. -/
theorem near_carry_frame (a : Int) (r : Nat) (t : Int → Bool) (q : Int)
    (hq : q<a+27 ∨ a+35+(r : Int)≤q) :
    put (clearRange (put (put t (a+27) true) (a+30) false) (a+31) (a+35+(r : Int)))
      (a+34+(r : Int)) true q=t q := by
  have h0 : q≠a+34+(r : Int) := by omega
  have h1 : ¬ (a+31≤q ∧ q<a+35+(r : Int)) := by omega
  have h2 : q≠a+30 := by omega
  have h3 : q≠a+27 := by omega
  simp [put,clearRange,h0,h1,h2,h3]

/-- The prepared absent-marker cycle reaches state 83 after its updated
bank return and nearby carry, retaining the bank suffix and left frame. -/
theorem padded_absent_near_carry (a : Int) (r v : Nat) (rest : List Nat)
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
    ∃ (mid e : Config 284), mid.state=23 ∧ e.state=23 ∧
      let output := put (clearRange (put (put e.tape (a+27) true) (a+30) false)
        (a+31) (a+35+(r : Int))) (a+34+(r : Int)) true
      silentSegment machine (cfg 93 a t) (cfg 83 (a+26) output)
        (((((((((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28+(r+8))+(r+32))+28)+(r+6))+
          (v+3+(encode (rest ++ [0])).length))+
          ((encode ((v+1)::(rest ++ [0]))).length+(r+5)+2))+(2*r+17)) ∧
      Holds output (a+36+(r : Int))
        ((encode ((v+1)::(rest ++ [0])) ++ [false,false]) ++ suffix) ∧
      output (a-3)=false ∧ (∀ q, q<a+26 → output q=t q) := by
  obtain ⟨mid,e,hs,he,hseg,hbank,_hmissing,hleft,h27,h28,h29,hrun⟩ :=
    padded_absent_increment_return1_with_control a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  let output := put (clearRange (put (put e.tape (a+27) true) (a+30) false)
    (a+31) (a+35+(r : Int))) (a+34+(r : Int)) true
  have hcarry := near_carry_to83 a r e.tape h27 h28 h29 hrun
  have hall := segAdd machine _ _ _ _ (2*r+17) hseg hcarry
  have hbank' : Holds output (a+36+(r : Int))
      ((encode ((v+1)::(rest ++ [0])) ++ [false,false]) ++ suffix) := by
    apply holds_transport e.tape output _ _ hbank
    intro q hq _
    symm
    exact near_carry_frame a r e.tape q (Or.inr (by omega))
  have hleft' : ∀ q, q<a+26 → output q=t q := by
    intro q hq
    calc
      output q = e.tape q := near_carry_frame a r e.tape q (Or.inl (by omega))
      _ = t q := hleft q hq
  have hmissing : output (a-3)=false := (hleft' _ (by omega)).trans absent
  exact ⟨mid,e,hs,he,hall,hbank',hmissing,hleft'⟩

#print axioms padded_absent_near_carry
#print axioms near_carry_frame
#print axioms near_carry_to83
end Shared.Beeping.NPcoNP.NativeAllZeroNearCarry
