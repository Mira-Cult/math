import Shared.Beeping.NPcoNP.NativeAllZeroNextSelector
import Shared.Beeping.NPcoNP.NativeAllZeroTerminalReady

/-! A marker-present all-zero dispatch followed by the unit/terminal
operation. This is a supplied-layout theorem, not a recurrence proof. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroTerminalReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeAllZeroToUnit
open Shared.Beeping.NPcoNP.NativeAllZeroNextSelector
open Shared.Beeping.NPcoNP.NativeAllZeroTerminalReady
open Shared.Beeping.NPcoNP.NativeUnitTerminalLayoutExact
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
attribute [local irreducible] machine

/-- With an earlier marker and a delimited bank, the literal machine
finishes the fill, increments the first bank value, and returns to state 83
in two finite silent segments. No reachability is assumed. -/
theorem all_zero_terminal_return_detailed (a : Int) (r v : Nat) (rest : List Nat)
    (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (earlier : t (a-1)=true)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false,false])) :
    ∃ mid : Config 284, mid.state=23 ∧
      silentSegment machine (cfg 93 a t) mid
        ((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length))) ∧
      let final := setAt (a+29) (setAt (a+30) mid.tape)
      Holds final (a+2) (markerWindow (List.replicate 12 0 ++ [3,r])) ∧
      final (a+1)=true ∧
      Holds final (a+36+(r : Int)) (encode ((v+1)::rest) ++ [false]) ∧
      Holds final (a+33+(r : Int)) (List.replicate 2 true ++ [false]) ∧
      (∀ q, q≠a+29 →
        (q<a+30 ∨ a+36+(r : Int)+(((v+1)+(encode rest).length : Nat):Int)<q) →
        final q=t q) ∧
      silentSegment machine mid (cfg 83 (a+32+(r : Int)) final)
        ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12)) := by
  have ⟨hword,hleft⟩ := filled_window a r t window marker nextZero h1
  have hpre : filled a r t (a+29)=false := by
    rw [filled_before a r t (a+29) (by omega)]
    exact nextZero
  have hbits : t (a+1)=true ∧ t (a+2)=false := by
    have h1' := holds_get t a (markerWindow (List.replicate 13 0 ++ [0])) window 1 (by decide)
    have h2' := holds_get t a (markerWindow (List.replicate 13 0 ++ [0])) window 2 (by decide)
    have b1 : (markerWindow (List.replicate 13 0 ++ [0]))[1]=true := by decide
    have b2 : (markerWindow (List.replicate 13 0 ++ [0]))[2]=false := by decide
    rw [b1] at h1'
    rw [b2] at h2'
    exact ⟨by simpa using h1',by simpa using h2'⟩
  have hbefore : filled a r t (a+1)=true := by
    rw [filled_before a r t (a+1) (by omega)]
    exact hbits.1
  have hleft0 : filled a r t (a+2)=false := by
    rw [filled_before a r t (a+2) (by omega)]
    exact hbits.2
  have hlen : (encode (List.replicate 11 0 ++ [1,0,r])).length=r+29 := by
    simp [encode_append,encode,block_length,zeros_length]
    omega
  have hmark : filled a r t (a+33+(r : Int))=true := by
    change (if a+32≤a+33+(r : Int) ∧ a+33+(r : Int)<a+34+(r : Int)
      then true else setAt (a+30) t (a+33+(r : Int)))=true
    rw [if_pos (by omega)]
  have hterm := unit_terminal_next_layout_exact (filled a r t) (a+4) a 11 r (r+3) v [] rest
    hword (by simp) (by omega)
    (by
      have hp : a+4+((2*11 : Nat):Int)+3=a+29 := by norm_num; omega
      rw [hp]; exact hpre)
    (by
      have hp : a+4+((2*11 : Nat):Int)+6=a+32 := by norm_num; omega
      rw [hp]; exact filled_scanword a r t hm delimiter)
    (by
      have hp : a+4+((2*11 : Nat):Int)+6+((r+3 : Nat):Int)+1=a+36+(r : Int) := by
        push_cast; omega
      rw [hp]; exact filled_bank a r t _ bank)
    (by norm_num; omega)
    (filled_terminal_window a r t window marker)
    (filled_earlier_marker a r t earlier)
    (by
      have hp : a+4-2=a+2 := by omega
      rw [hp]; exact hleft0)
    (by
      have hp : a+4-1=a+3 := by omega
      rw [hp]; exact hleft)
    (by
      have hp : a+4-3=a+1 := by omega
      rw [hp]; exact hbefore)
    (by
      change filled a r t (a+4+((encode (List.replicate 11 0 ++ [1,0,r])).length : Int))=true
      rw [hlen]
      have hp : a+4+((r+29 : Nat):Int)=a+33+(r : Int) := by push_cast; omega
      rw [hp]; exact hmark)
    (by
      change a+4+((encode (List.replicate 11 0 ++ [1,0,r])).length : Int)=_
      rw [hlen]
      push_cast; omega)
  dsimp only at hterm
  obtain ⟨mid,hs,hfirst,_hlen,hwindow,hbefore',_hmarker,hbank,hext,hframe,_hhead,hreturn⟩ := hterm
  rw [hlen] at hext
  simp only [Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat, Int.reduceAdd,
    Nat.cast_add, Int.add_assoc, List.nil_append] at hwindow hbefore' hbank hext hframe hreturn
  have hd : a+30-1=a+29 := by omega
  have hw : a+4-2=a+2 := by omega
  have hb : a+4-3=a+1 := by omega
  have hp : a+(32+((r : Int)+4))=a+36+(r : Int) := by omega
  have hx : a+(4+((r : Int)+29))=a+33+(r : Int) := by omega
  have hh : a+(30+((r : Int)+3))-1=a+32+(r : Int) := by omega
  rw [hd,hw] at hwindow
  rw [hd,hb] at hbefore'
  rw [hd,hp] at hbank
  rw [hd,hx] at hext
  rw [hd,hp] at hframe
  rw [hd,hh] at hreturn
  have hframe' : ∀ q, q≠a+29 →
      (q<a+30 ∨ a+36+(r : Int)+(((v+1)+(encode rest).length : Nat):Int)<q) →
      setAt (a+29) (setAt (a+30) mid.tape) q=t q := by
    intro q hne hout
    have hf := hframe q hne (by
      rcases hout with hleft | hright
      · left; omega
      · right
        push_cast at hright ⊢
        omega)
    rw [hf]
    rcases hout with hleft | hright
    · exact filled_before a r t q hleft
    · exact filled_after a r t q (by omega)
  have hfill := fill_to_next_selector a r t window marker nextZero h0 h1 hz hm
  have hfirst' := segAdd machine _ _ _ (2*r+66)
    ((2*11+4)+((r+3)+v+6+(encode rest).length)) hfill hfirst
  refine ⟨mid,hs,hfirst',?_,?_,?_,?_,?_,?_⟩
  · exact hwindow
  · exact hbefore'
  · exact hbank
  · exact hext
  · exact hframe'
  · exact hreturn

#print axioms all_zero_terminal_return_detailed

/-- The existing framed interface omits the selector extension. -/
theorem all_zero_terminal_return_framed (a : Int) (r v : Nat) (rest : List Nat)
    (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (earlier : t (a-1)=true)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false,false])) :
    ∃ mid : Config 284, mid.state=23 ∧
      silentSegment machine (cfg 93 a t) mid
        ((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length))) ∧
      let final := setAt (a+29) (setAt (a+30) mid.tape)
      Holds final (a+2) (markerWindow (List.replicate 12 0 ++ [3,r])) ∧
      final (a+1)=true ∧
      Holds final (a+36+(r : Int)) (encode ((v+1)::rest) ++ [false]) ∧
      (∀ q, q≠a+29 →
        (q<a+30 ∨ a+36+(r : Int)+(((v+1)+(encode rest).length : Nat):Int)<q) →
        final q=t q) ∧
      silentSegment machine mid (cfg 83 (a+32+(r : Int)) final)
        ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12)) := by
  obtain ⟨mid,hs,hfirst,hwindow,hbefore,hbank,_hext,hframe,hreturn⟩ :=
    all_zero_terminal_return_detailed a r v rest t window earlier marker nextZero h0 h1 hz hm delimiter bank
  exact ⟨mid,hs,hfirst,hwindow,hbefore,hbank,hframe,hreturn⟩

#print axioms all_zero_terminal_return_framed

/-- The original interface remains available to callers that do not need
the untouched-tape frame. -/
theorem all_zero_terminal_return (a : Int) (r v : Nat) (rest : List Nat)
    (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (earlier : t (a-1)=true)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int)) (encode (v::rest) ++ [false,false])) :
    ∃ mid : Config 284, mid.state=23 ∧
      silentSegment machine (cfg 93 a t) mid
        ((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length))) ∧
      let final := setAt (a+29) (setAt (a+30) mid.tape)
      Holds final (a+2) (markerWindow (List.replicate 12 0 ++ [3,r])) ∧
      final (a+1)=true ∧
      Holds final (a+36+(r : Int)) (encode ((v+1)::rest) ++ [false]) ∧
      silentSegment machine mid (cfg 83 (a+32+(r : Int)) final)
        ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12)) := by
  obtain ⟨mid,hs,hfirst,hwindow,hbefore,hbank,_hframe,hreturn⟩ :=
    all_zero_terminal_return_framed a r v rest t window earlier marker nextZero h0 h1 hz hm delimiter bank
  exact ⟨mid,hs,hfirst,hwindow,hbefore,hbank,hreturn⟩

#print axioms all_zero_terminal_return
end Shared.Beeping.NPcoNP.NativeAllZeroTerminalReturn
