import Shared.Beeping.NPcoNP.NativeUniformSuffixFrame
import Shared.Beeping.NPcoNP.NativeAllZeroNextReturn
import Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch

/-! Upgrade the absent-marker increment's arbitrary finite suffix guarantee to
an exact right-hand frame, using its suffix-independent literal duration. -/
namespace Shared.Beeping.NPcoNP.NativeAbsentIncrementRightFrame
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeGrammarAdministrativeDispatch
open Shared.Beeping.NPcoNP.NativeAllZeroNextReturn
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativePositiveThreeCycle
open Shared.Beeping.NPcoNP.NativeUniformSuffixFrame
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 30000000

def duration (r v : Nat) (rest : List Nat) : Nat :=
  ((((((((((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length)))+
    ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12))+
    ((2*r+74+2*(bankSuffix v rest).length)+(3*(r+3)+18)))+31)+28+(r+8))+(r+32))+28)+(r+6))+
    (v+3+(encode (rest ++ [0])).length))+
    ((encode ((v+1)::(rest ++ [0]))).length+(r+5)+2))

theorem return1_right_frame (a : Int) (r v : Nat) (rest : List Nat) (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (left0 : t (a-2)=false) (earlier : t (a-1)=true) (absent : t (a-3)=false)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true) (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int)) ((encode (v::rest) ++ [false,false,false]) ++ [false,false]))
    (e : Config 284)
    (segment : silentSegment machine (cfg 93 a t) (cfg 1 (a+27) e.tape) (duration r v rest)) :
    ∀ q, a+36+(r : Int)+(((encode (v::rest) ++ [false,false,false]) ++ [false,false]).length : Int)≤q →
      e.tape q=t q := by
  let base := a+36+(r : Int)
  let inputWord := (encode (v::rest) ++ [false,false,false]) ++ [false,false]
  let outputWord := encode ((v+1)::(rest++[0])) ++ [false,false]
  have hlen : inputWord.length=outputWord.length := by
    simp [inputWord,outputWord,encode_append,encode,block_length]
    omega
  have hs : ∀ xs, Holds t (base+((inputWord.length : Nat):Int)) xs →
      ∃ out : Config 284, silentSegment machine (cfg 93 a t) out (duration r v rest) ∧
        Holds out.tape (base+((inputWord.length : Nat):Int)) xs := by
    intro xs hx
    have hall : Holds t base (inputWord ++ xs) := holds_append_intro t base inputWord xs bank hx
    have hbank : Holds t base ((encode (v::rest) ++ [false,false,false]) ++ ([false,false] ++ xs)) := by
      simpa only [inputWord,List.append_assoc] using hall
    obtain ⟨mid,out,_,_,hseg,hout,_,_,_,_,_,_,_⟩ :=
      padded_absent_increment_return1_with_marker a r v rest xs t window left0 earlier absent
        marker nextZero h0 h1 hz hm delimiter hbank
    have hsplit := holds_split out.tape base outputWord xs (by
      simpa only [outputWord] using hout)
    refine ⟨cfg 1 (a+27) out.tape,?_,?_⟩
    · simpa only [duration] using hseg
    · simpa only [hlen,cfg] using hsplit.2
  have hf := frame_of_uniform_suffix machine (cfg 93 a t) (cfg 1 (a+27) e.tape)
    (duration r v rest) (base+((inputWord.length : Nat):Int)) segment hs
  simpa only [base,inputWord,cfg] using hf

#print axioms return1_right_frame
end Shared.Beeping.NPcoNP.NativeAbsentIncrementRightFrame
