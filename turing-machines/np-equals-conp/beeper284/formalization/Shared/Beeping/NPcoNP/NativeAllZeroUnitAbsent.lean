import Shared.Beeping.NPcoNP.NativeAllZeroNearCarry
import Shared.Beeping.NPcoNP.NativeTerminalUnitSelector

/-! The returned unit selector with the earlier marker absent. This is a
prepared-layout result, not a blank-start or graph-refinement theorem. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.NativeAllZeroNextReturn
open Shared.Beeping.NPcoNP.NativeAllZeroNearCarry
open Shared.Beeping.NPcoNP.NativeTerminalUnitSelector
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000
attribute [local irreducible] machine

def zeroWord : List Bool := markerWindow (List.replicate 13 0 ++ [0])
def unitWord : List Bool := markerWindow (List.replicate 13 0 ++ [1])

theorem unit_word_split : unitWord=[false,true] ++ zeroWord.take 26 ++ [true] := by decide

/-- An absent earlier marker sends the marked unit window back to state 93
at the old anchor in 32 silent tape-preserving steps. -/
theorem unit_absent_dispatch (a : Int) (t : Int → Bool)
    (window : Holds t (a-2) unitWord) (absent : t (a-3)=false) :
    silentSegment machine (cfg 83 (a+26) t) (cfg 93 a t) 32 := by
  let xs := List.replicate 13 0 ++ [1]
  have hlen : (encode xs).length=29 := by decide
  have hs := marker_window_to92 t (a-2) xs (by simp [xs]) window
  rw [hlen] at hs
  have hp : a-2+((29 : Nat):Int)-1=a+26 := by omega
  rw [hp,show a-2-1=a-3 by omega] at hs
  have h0 : t (a-2)=false := by
    have h := holds_get t (a-2) unitWord window 0 (by decide)
    have hb : unitWord[0]=false := by decide
    rw [hb] at h
    simpa using h
  have h1 : t (a-1)=true := by
    have h := holds_get t (a-2) unitWord window 1 (by decide)
    have hb : unitWord[1]=true := by decide
    rw [hb] at h
    have hp1 : a-2+(1:Int)=a-1 := by omega
    simpa [hp1] using h
  have hfirst : silentSegment machine (cfg 92 (a-3) t) (cfg 92 (a-2) t) 1 := by
    simpa only [show a-3+1=a-2 by omega] using oneSeg machine _ _ (step92_zero (a-3) t absent)
  have hsecond : silentSegment machine (cfg 92 (a-2) t) (cfg 92 (a-1) t) 1 := by
    simpa only [show a-2+1=a-1 by omega] using oneSeg machine _ _ (step92_zero (a-2) t h0)
  have hthird : silentSegment machine (cfg 92 (a-1) t) (cfg 93 a t) 1 := by
    simpa only [show a-1+1=a by omega] using oneSeg machine _ _ (step92_one (a-1) t h1)
  have h12 := segAdd machine _ _ _ 1 1 hfirst hsecond
  have h123 := segAdd machine _ _ _ 2 1 h12 hthird
  have hall := segAdd machine _ _ _ 29 3 hs h123
  simpa using hall

/-- A preserved initial window, its two cells to the left and a new right
marker form the next complete unit selector window. -/
theorem unit_window_of_frame (a : Int) (t out : Int → Bool)
    (window : Holds t a zeroWord) (left0 : t (a-2)=false) (left1 : t (a-1)=true)
    (frame : ∀ q, q<a+26 → out q=t q) (right : out (a+26)=true) :
    Holds out (a-2) unitWord := by
  have hprefix0 : Holds t a (zeroWord.take 26) := by
    have hs : zeroWord.take 26 ++ zeroWord.drop 26=zeroWord := List.take_append_drop 26 zeroWord
    apply holds_prefix_word t a _ (zeroWord.drop 26)
    rw [hs]
    exact window
  have hlen : (zeroWord.take 26).length=26 := by decide
  have hprefix : Holds out a (zeroWord.take 26) := by
    apply holds_transport t out _ _ hprefix0
    intro q _ hq
    rw [hlen] at hq
    symm
    exact frame q (by omega)
  have hpair : Holds out (a-2) [false,true] := by
    simp only [Holds]
    refine ⟨?_,?_,trivial⟩
    · rw [frame _ (by omega)]; exact left0
    · have hp : a-2+1=a-1 := by omega
      rw [hp,frame _ (by omega)]; exact left1
  have hright : Holds out (a+26) [true] := by simpa [Holds] using right
  have htail := holds_append_intro out a (zeroWord.take 26) [true] hprefix (by
    have hp : a+((zeroWord.take 26).length : Int)=a+26 := by rw [hlen]; norm_num
    rw [hp]
    exact hright)
  have hall := holds_append_intro out (a-2) [false,true] (zeroWord.take 26 ++ [true]) hpair (by
    have hp : a-2+(([false,true].length : Nat):Int)=a := by norm_num
    rw [hp]
    exact htail)
  rw [unit_word_split]
  simpa [List.append_assoc] using hall

/-- The supplied absent-marker cycle returns through its unit selector to
state 93 at the original anchor, retaining its updated bank and left frame. -/
theorem padded_absent_unit_next93_with_bits (a : Int) (r v : Nat) (rest : List Nat)
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
    ∃ (mid e : Config 284), mid.state=23 ∧ e.state=23 ∧
      let output := put (clearRange (put (put e.tape (a+27) true) (a+30) false)
        (a+31) (a+35+(r : Int))) (a+34+(r : Int)) true
      silentSegment machine (cfg 93 a t) (cfg 93 a output)
        ((((((((((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28+(r+8))+(r+32))+28)+(r+6))+
          (v+3+(encode (rest ++ [0])).length))+
          ((encode ((v+1)::(rest ++ [0]))).length+(r+5)+2))+(2*r+17))+32) ∧
      Holds output (a-2) unitWord ∧ output (a-3)=false ∧
      Holds output (a+36+(r : Int))
        ((encode ((v+1)::(rest ++ [0])) ++ [false,false]) ++ suffix) ∧
      (∀ q, q<a+26 → output q=t q) ∧
      output (a+27)=true ∧ output (a+28)=false := by
  obtain ⟨mid,e,hs,he,hseg,hbank,_hmissing,hleft,h27,h28,h29,hrun,h26⟩ :=
    padded_absent_increment_return1_with_marker a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  let output := put (clearRange (put (put e.tape (a+27) true) (a+30) false)
    (a+31) (a+35+(r : Int))) (a+34+(r : Int)) true
  have hcarry := near_carry_to83 a r e.tape h27 h28 h29 hrun
  have hframe : ∀ q, q<a+26 → output q=t q := by
    intro q hq
    calc
      output q=e.tape q := near_carry_frame a r e.tape q (Or.inl (by omega))
      _=t q := hleft q hq
  have hright : output (a+26)=true := by
    have hf : output (a+26)=e.tape (a+26) := near_carry_frame a r e.tape (a+26) (Or.inl (by omega))
    exact hf.trans h26
  have hwindow := unit_window_of_frame a t output window left0 earlier hframe hright
  have hmissing : output (a-3)=false := (hframe _ (by omega)).trans absent
  have hdispatch := unit_absent_dispatch a output hwindow hmissing
  have hall := segAdd machine _ _ _ _ (2*r+17) hseg hcarry
  have hall' := segAdd machine _ _ _ _ 32 hall hdispatch
  have hbank' : Holds output (a+36+(r : Int))
      ((encode ((v+1)::(rest ++ [0])) ++ [false,false]) ++ suffix) := by
    apply holds_transport e.tape output _ _ hbank
    intro q hq _
    symm
    exact near_carry_frame a r e.tape q (Or.inr (by omega))
  have hmark27 : output (a+27)=true := by
    simp [output,put,clearRange]
  have hzero28 : output (a+28)=false := by
    have hn : a+28≠a+34+(r : Int) := by omega
    simp [output,put,clearRange,hn,h28]
  exact ⟨mid,e,hs,he,hall',hwindow,hmissing,hbank',hframe,hmark27,hzero28⟩

/-- Retain the earlier next-state-93 interface. -/
theorem padded_absent_unit_next93 (a : Int) (r v : Nat) (rest : List Nat)
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
    ∃ (mid e : Config 284), mid.state=23 ∧ e.state=23 ∧
      let output := put (clearRange (put (put e.tape (a+27) true) (a+30) false)
        (a+31) (a+35+(r : Int))) (a+34+(r : Int)) true
      silentSegment machine (cfg 93 a t) (cfg 93 a output)
        ((((((((((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28+(r+8))+(r+32))+28)+(r+6))+
          (v+3+(encode (rest ++ [0])).length))+
          ((encode ((v+1)::(rest ++ [0]))).length+(r+5)+2))+(2*r+17))+32) ∧
      Holds output (a-2) unitWord ∧ output (a-3)=false ∧
      Holds output (a+36+(r : Int))
        ((encode ((v+1)::(rest ++ [0])) ++ [false,false]) ++ suffix) ∧
      (∀ q, q<a+26 → output q=t q) := by
  obtain ⟨mid,e,hs,he,hseg,hwindow,hmissing,hbank,hframe,_hmark,_hzero⟩ :=
    padded_absent_unit_next93_with_bits a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  exact ⟨mid,e,hs,he,hseg,hwindow,hmissing,hbank,hframe⟩

theorem unit_word_drop : unitWord.drop 2 = markerWindow (List.replicate 12 0 ++ [1]) := by decide

/-- From state 93 the returned unit window takes the state-260 branch. -/
theorem unit_window_to260 (a : Int) (t : Int → Bool)
    (window : Holds t (a-2) unitWord)
    (marker : t (a+27)=true) (nextZero : t (a+28)=false) :
    silentSegment machine (cfg 93 a t) (cfg 260 (a+28) t) 28 := by
  have hsplit : unitWord=[false,true] ++ unitWord.drop 2 := by decide
  have hw := window
  rw [hsplit] at hw
  have ht := holds_append_tail t (a-2) [false,true] (unitWord.drop 2) hw
  have hp : a-2+(([false,true].length : Nat):Int)=a := by norm_num
  rw [hp,unit_word_drop] at ht
  have hm : t (a+((2*12 : Nat):Int)+3)=true := by
    have he : a+((2*12 : Nat):Int)+3=a+27 := by norm_num; omega
    rw [he]
    exact marker
  have hz : t (a+((2*12 : Nat):Int)+4)=false := by
    have he : a+((2*12 : Nat):Int)+4=a+28 := by norm_num; omega
    rw [he]
    exact nextZero
  have h260 := terminal_unit_to260 t a 12 ht hm hz
  have hp' : a+((2*12 : Nat):Int)+4=a+28 := by norm_num; omega
  have hc : 2*12+4=28 := by decide
  simpa only [hp',hc] using h260

/-- The absent-marker return and following selector reach state 260 in 60
silent transitions, with the entire tape unchanged. -/
theorem unit_absent_to260 (a : Int) (t : Int → Bool)
    (window : Holds t (a-2) unitWord) (absent : t (a-3)=false)
    (marker : t (a+27)=true) (nextZero : t (a+28)=false) :
    silentSegment machine (cfg 83 (a+26) t) (cfg 260 (a+28) t) 60 := by
  have h93 := unit_absent_dispatch a t window absent
  have h260 := unit_window_to260 a t window marker nextZero
  have hall := segAdd machine _ _ _ 32 28 h93 h260
  simpa using hall

/-- Continue the supplied cycle through the state-260 branch. -/
theorem padded_absent_unit_next260 (a : Int) (r v : Nat) (rest : List Nat)
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
    ∃ (mid e : Config 284), mid.state=23 ∧ e.state=23 ∧
      let output := put (clearRange (put (put e.tape (a+27) true) (a+30) false)
        (a+31) (a+35+(r : Int))) (a+34+(r : Int)) true
      silentSegment machine (cfg 93 a t) (cfg 260 (a+28) output)
        (((((((((((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28+(r+8))+(r+32))+28)+(r+6))+
          (v+3+(encode (rest ++ [0])).length))+
          ((encode ((v+1)::(rest ++ [0]))).length+(r+5)+2))+(2*r+17))+32)+28) ∧
      Holds output (a-2) unitWord ∧ output (a-3)=false ∧
      Holds output (a+36+(r : Int))
        ((encode ((v+1)::(rest ++ [0])) ++ [false,false]) ++ suffix) ∧
      (∀ q, q<a+26 → output q=t q) ∧
      output (a+27)=true ∧ output (a+28)=false := by
  obtain ⟨mid,e,hs,he,hseg,hwindow,hmissing,hbank,hframe,hmark,hzero⟩ :=
    padded_absent_unit_next93_with_bits a r v rest suffix t window left0 earlier absent
      marker nextZero h0 h1 hz hm delimiter bank
  let output := put (clearRange (put (put e.tape (a+27) true) (a+30) false)
    (a+31) (a+35+(r : Int))) (a+34+(r : Int)) true
  have hnext := unit_window_to260 a output hwindow hmark hzero
  have hall := segAdd machine _ _ _ _ 28 hseg hnext
  exact ⟨mid,e,hs,he,hall,hwindow,hmissing,hbank,hframe,hmark,hzero⟩

#print axioms padded_absent_unit_next260
#print axioms unit_window_to260
#print axioms padded_absent_unit_next93_with_bits
#print axioms unit_word_drop
#print axioms unit_absent_to260
#print axioms padded_absent_unit_next93
#print axioms unit_word_split
#print axioms unit_absent_dispatch
#print axioms unit_window_of_frame
end Shared.Beeping.NPcoNP.NativeAllZeroUnitAbsent
