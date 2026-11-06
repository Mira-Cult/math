import Shared.Beeping.NPcoNP.NativeAllZeroTerminalSuffix
import Shared.Beeping.NPcoNP.NativePositiveThreeCycle

/-! Compose the all-zero dispatch with the exact positive-selector cycle.
The supplied layout is not an invariant or a blank-start reachability claim. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroPositiveCycle
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeAllZeroTerminalReturn
open Shared.Beeping.NPcoNP.NativeAllZeroTerminalSuffix
open Shared.Beeping.NPcoNP.NativeThreeCarryReturnExact
open Shared.Beeping.NPcoNP.NativeThreeCarryNextWindow
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.NativeManyTerminalWindow
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
attribute [local irreducible] machine

/-- The selector operation and its following return leave every cell left of
the new marker unchanged. -/
theorem cycle_left (a : Int) (r v : Nat) (rest : List Nat) (t : Int → Bool)
    (q : Int) (hq : q<a+26) :
    outTape (a+30) (r+3) (selectorOutput a r v rest t) q=t q := by
  rw [output_left (a+30) (r+3) _ q (by omega)]
  change spec (clearAt (a+30) t)
    (a+36+(r : Int)+2+((bankSuffix v rest).length : Int))
    ((bankSuffix v rest).length+2) q=t q
  rw [spec_outside _ _ _ _ (Or.inl (by push_cast; omega))]
  change (if q=a+30 then false else t q)=t q
  rw [if_neg (by omega)]

/-- The positive terminal window determines the later scan cell. -/
theorem terminal_window_bit (t : Int → Bool) (a : Int) (r : Nat)
    (window : Holds t (a+2) (markerWindow (List.replicate 12 0 ++ [3,r]))) :
    t (a+31)=false := by
  have hw := window
  rw [terminal_many_window 12 0 r] at hw
  have hblock := holds_append_tail t (a+2+1) (encode (List.replicate 12 0))
    (block (0+3) ++ List.replicate (r+1) true) hw.2
  have hpblock : a+2+1+((encode (List.replicate 12 0)).length : Int)=a+27 := by
    rw [zeros_length]
    norm_num
    omega
  rw [hpblock] at hblock
  have hb := holds_prefix_word t (a+27) (block 3) (List.replicate (r+1) true) hblock
  simp only [block,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds] at hb
  have hp : a+27+1+1+1+1=a+31 := by omega
  simpa only [hp] using hb.2.2.2.2.1

/-- With three supplied bank sentinels, a marker-present all-zero dispatch
and the following positive-selector cycle reach the next all-zero window in
an exact finite silent segment. The next earlier-marker value is preserved. -/
theorem all_zero_positive_cycle_framed_with_bits (a : Int) (r v : Nat) (rest : List Nat)
    (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (left0 : t (a-2)=false) (earlier : t (a-1)=true)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false,false,false])) :
    ∃ mid : Config 284, mid.state=23 ∧
      let t1 := setAt (a+29) (setAt (a+30) mid.tape)
      let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
      silentSegment machine (cfg 93 a t) (cfg 83 (a+25) final)
        (((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18))) ∧
      Holds final (a-2) (markerWindow (List.replicate 13 0 ++ [0])) ∧
      final (a-3)=t (a-3) ∧ final (a+26)=true ∧
      Holds final (a+36+(r : Int)) (encode (v::rest) ++ [true,false,false]) ∧
      (∀ q, q<a+26 → final q=t q) ∧
      (∀ q, a+36+(r : Int)+2+((bankSuffix v rest).length : Int)<q →
        a+36+(r : Int)+(((v+1)+(encode rest).length : Nat):Int)<q → final q=t q) ∧
      t1 (a+31)=false ∧ t1 (a+35+(r : Int))=false := by
  have hbank2 : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false,false]) := by
    apply holds_prefix_word t _ (encode (v::rest) ++ [false,false]) [false]
    simpa [List.append_assoc] using bank
  obtain ⟨mid,hs,hfirst,hwindow,_hbefore,_hbank,hext,hframe,hreturn⟩ :=
    all_zero_terminal_return_detailed a r v rest t window earlier marker nextZero h0 h1 hz hm delimiter hbank2
  have hbank3 : Holds t (a+36+(r : Int)) ((encode (v::rest) ++ [false,false]) ++ [false]) := by
    simpa [List.append_assoc] using bank
  obtain ⟨mid',_hs',hfirst',_hwindow',_hbefore',hbank',_hframe',_hreturn'⟩ :=
    all_zero_terminal_return_suffix a r v rest [false] t window earlier marker nextZero h0 h1 hz hm delimiter hbank3
  have heq : mid=mid' := hfirst.1.symm.trans hfirst'.1
  subst mid'
  let t1 := setAt (a+29) (setAt (a+30) mid.tape)
  let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
  have hbank'' : Holds t1 (a+36+(r : Int)) (encode ((v+1)::rest) ++ [false,false]) := by
    simpa [t1,List.append_assoc] using hbank'
  have hold : Holds t1 a (markerWindow (List.replicate 13 0 ++ [0])) := by
    apply holds_transport t t1 _ _ window
    intro q _ hq
    have hlen : (markerWindow (List.replicate 13 0 ++ [0])).length=28 := by decide
    rw [hlen] at hq
    symm
    exact hframe q (by omega) (Or.inl (by omega))
  have hleft0 : t1 (a-2)=false := by
    change setAt (a+29) (setAt (a+30) mid.tape) (a-2)=false
    rw [hframe _ (by omega) (Or.inl (by omega))]
    exact left0
  have hleft1 : t1 (a-1)=true := by
    change setAt (a+29) (setAt (a+30) mid.tape) (a-1)=true
    rw [hframe _ (by omega) (Or.inl (by omega))]
    exact earlier
  obtain ⟨hcycle,hnext,hbefore,hmarker,hbankout⟩ :=
    positive_three_cycle a r v rest t1 hold hleft0 hleft1 hwindow hext hbank''
  have hfirstReturn := segAdd machine _ _ _
    ((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))
    ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))
    hfirst hreturn
  have hall := segAdd machine _ _ _
    (((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
      ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12)))
    ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)) hfirstReturn hcycle
  have hleftFrame : ∀ q, q<a+26 → final q=t q := by
    intro q hq
    calc
      final q = t1 q := cycle_left a r v rest t1 q hq
      _ = t q := hframe q (by omega) (Or.inl (by omega))
  have hbefore' : final (a-3)=t (a-3) := hleftFrame _ (by omega)
  have hrightFrame : ∀ q, a+36+(r : Int)+2+((bankSuffix v rest).length : Int)<q →
      a+36+(r : Int)+(((v+1)+(encode rest).length : Nat):Int)<q → final q=t q := by
    intro q hq hb
    calc
      final q = selectorOutput a r v rest t1 q := by
        apply return_output_right (a+30) (r+3) _ q (by omega)
        push_cast at hq ⊢
        omega
      _ = clearAt (a+30) t1 q := by
        unfold selectorOutput
        apply spec_outside
        exact Or.inr hq
      _ = t1 q := by
        change (if q=a+30 then false else t1 q)=t1 q
        rw [if_neg (by push_cast at hq; omega)]
      _ = t q := hframe q (by push_cast at hq; omega) (Or.inr hb)
  have hcell : t1 (a+31)=false := terminal_window_bit t1 a r hwindow
  have hdelim : t1 (a+35+(r : Int))=false := by
    have hext' := hext
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds] at hext'
    have hp : a+33+(r : Int)+1+1=a+35+(r : Int) := by omega
    simpa only [hp] using hext'.2.2.1
  exact ⟨mid,hs,hall,hnext,hbefore',hmarker,hbankout,hleftFrame,hrightFrame,hcell,hdelim⟩


/-- Retain the earlier one-cell interface for existing clients. -/
theorem all_zero_positive_cycle_framed_with_bit (a : Int) (r v : Nat) (rest : List Nat)
    (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (left0 : t (a-2)=false) (earlier : t (a-1)=true)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false,false,false])) :
    ∃ mid : Config 284, mid.state=23 ∧
      let t1 := setAt (a+29) (setAt (a+30) mid.tape)
      let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
      silentSegment machine (cfg 93 a t) (cfg 83 (a+25) final)
        (((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18))) ∧
      Holds final (a-2) (markerWindow (List.replicate 13 0 ++ [0])) ∧
      final (a-3)=t (a-3) ∧ final (a+26)=true ∧
      Holds final (a+36+(r : Int)) (encode (v::rest) ++ [true,false,false]) ∧
      (∀ q, q<a+26 → final q=t q) ∧
      (∀ q, a+36+(r : Int)+2+((bankSuffix v rest).length : Int)<q →
        a+36+(r : Int)+(((v+1)+(encode rest).length : Nat):Int)<q → final q=t q) ∧
      t1 (a+31)=false := by
  obtain ⟨mid,hs,hseg,hwindow,hbefore,hmarker,hbank,hleft,hright,hcell,_hdelim⟩ :=
    all_zero_positive_cycle_framed_with_bits a r v rest t window left0 earlier marker nextZero h0 h1 hz hm delimiter bank
  exact ⟨mid,hs,hseg,hwindow,hbefore,hmarker,hbank,hleft,hright,hcell⟩

/-- The original framed interface is retained for existing clients. -/
theorem all_zero_positive_cycle_framed (a : Int) (r v : Nat) (rest : List Nat)
    (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (left0 : t (a-2)=false) (earlier : t (a-1)=true)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false,false,false])) :
    ∃ mid : Config 284, mid.state=23 ∧
      let t1 := setAt (a+29) (setAt (a+30) mid.tape)
      let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
      silentSegment machine (cfg 93 a t) (cfg 83 (a+25) final)
        (((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18))) ∧
      Holds final (a-2) (markerWindow (List.replicate 13 0 ++ [0])) ∧
      final (a-3)=t (a-3) ∧ final (a+26)=true ∧
      Holds final (a+36+(r : Int)) (encode (v::rest) ++ [true,false,false]) ∧
      (∀ q, q<a+26 → final q=t q) ∧
      (∀ q, a+36+(r : Int)+2+((bankSuffix v rest).length : Int)<q →
        a+36+(r : Int)+(((v+1)+(encode rest).length : Nat):Int)<q → final q=t q) := by
  obtain ⟨mid,hs,hseg,hwindow,hbefore,hmarker,hbank,hleft,hright,_hcell⟩ :=
    all_zero_positive_cycle_framed_with_bit a r v rest t window left0 earlier marker nextZero h0 h1 hz hm delimiter bank
  exact ⟨mid,hs,hseg,hwindow,hbefore,hmarker,hbank,hleft,hright⟩

/-- The original local cycle interface, retained for existing clients. -/
theorem all_zero_positive_cycle (a : Int) (r v : Nat) (rest : List Nat)
    (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (left0 : t (a-2)=false) (earlier : t (a-1)=true)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false,false,false])) :
    ∃ mid : Config 284, mid.state=23 ∧
      let t1 := setAt (a+29) (setAt (a+30) mid.tape)
      let final := outTape (a+30) (r+3) (selectorOutput a r v rest t1)
      silentSegment machine (cfg 93 a t) (cfg 83 (a+25) final)
        (((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
          ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
          ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18))) ∧
      Holds final (a-2) (markerWindow (List.replicate 13 0 ++ [0])) ∧
      final (a-3)=t (a-3) ∧ final (a+26)=true ∧
      Holds final (a+36+(r : Int)) (encode (v::rest) ++ [true,false,false]) ∧
      (∀ q, q<a+26 → final q=t q) := by
  obtain ⟨mid,hs,hseg,hwindow,hbefore,hmark,hbank,hleft,_hright⟩ :=
    all_zero_positive_cycle_framed a r v rest t window left0 earlier marker nextZero h0 h1 hz hm delimiter bank
  exact ⟨mid,hs,hseg,hwindow,hbefore,hmark,hbank,hleft⟩

#print axioms terminal_window_bit
#print axioms all_zero_positive_cycle_framed_with_bits
#print axioms all_zero_positive_cycle_framed_with_bit
#print axioms all_zero_positive_cycle_framed
#print axioms cycle_left
#print axioms all_zero_positive_cycle
end Shared.Beeping.NPcoNP.NativeAllZeroPositiveCycle
