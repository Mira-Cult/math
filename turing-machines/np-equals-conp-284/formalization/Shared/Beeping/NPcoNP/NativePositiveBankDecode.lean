import Shared.Beeping.NPcoNP.NativeFifthPositive
import Shared.Beeping.NPcoNP.Bootstrap284BankDecode

/-! A finite decoder bridge for the positive physical bank result. This is an
extensional readback of an asserted tape word, not a graph execution theorem. -/
namespace Shared.Beeping.NPcoNP.NativePositiveBankDecode
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeBeepCarry
open Shared.Beeping.NPcoNP.NativeFifthPositive
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Decode the unchanged prefix, decremented target and appended zero reserve
from the exact finite output window, retaining the following blank. -/
theorem decode_updated_bank (t : Int → Bool) (start : Int)
    (values : List Nat) (v : Nat) (vs : List Nat)
    (hprefix : Holds t start (encode values))
    (updated : Holds t (start+((encode values).length : Int))
      (encode (v::vs) ++ [true,false,false])) :
    let all := values ++ (v::vs) ++ [0]
    decode all.length (readCells t start (encode all ++ [false]).length) =
      some (all,[false]) := by
  dsimp only
  let all := values ++ (v::vs) ++ [0]
  have hh := holds_append_intro t start (encode values)
    (encode (v::vs) ++ [true,false,false]) hprefix updated
  have he : encode all ++ [false] =
      encode values ++ (encode (v::vs) ++ [true,false,false]) := by
    simp [all,encode_append,encode,block,List.append_assoc]
  have hword : Holds t start (encode all ++ [false]) := by rw [he]; exact hh
  rw [read_of_holds t start (encode all ++ [false]) hword]
  exact decode_encode all [false]

/-- The conditional physical execution's observed bank decodes to the ten
unchanged values, decremented target, remaining values and new zero reserve. -/
theorem supplied_beep_fifth_positive_decodes (h b separator : Int) (t : Int → Bool)
    (ht : t h=true) (hm1 : t (h-1)=false) (hm2 : t (h-2)=false)
    (hm3 : t (h-3)=true) (hm4 : t (h-4)=true)
    (hp1 : t (h+1)=false) (hp2 : t (h+2)=false)
    (hlong : h+12≤separator)
    (ones : ∀ q, h+3≤q → q<separator → t q=true)
    (left : ∀ q, q<h-4 → t q=false)
    (hb : h<b) (right : ∀ q, b≤q → t q=false)
    (hsepzero : t separator=false) (xs : List Nat) (hxs : xs.length=4)
    (v : Nat) (vs : List Nat)
    (bank : Holds t (separator+1)
      (encode (List.replicate 6 0 ++ xs) ++ (encode ((v+1)::vs) ++ [false,false]))) :
    let values := List.replicate 6 0 ++ xs
    let pos := separator+1+((encode values).length : Int)
    let all := values ++ (v::vs) ++ [0]
    ∃ (n : Nat) (out : Int → Bool), 1<n ∧
      decode all.length (readCells out (separator+1) (encode all ++ [false]).length)=some (all,[false]) ∧
      physical.advance (cfg 99 h t) n=cfg 23 (pos-2) out ∧
      physical.wordFrom (cfg 99 h t) n=[true] := by
  dsimp only
  obtain ⟨n,out,hn,hprefix,hupdated,_hleft,ha,hw⟩ :=
    supplied_beep_fifth_positive h b separator t ht hm1 hm2 hm3 hm4 hp1 hp2
      hlong ones left hb right hsepzero xs hxs v vs bank
  have hdec := decode_updated_bank out (separator+1) (List.replicate 6 0 ++ xs) v vs hprefix hupdated
  exact ⟨n,out,hn,hdec,ha,hw⟩

#print axioms supplied_beep_fifth_positive_decodes
#print axioms decode_updated_bank
end Shared.Beeping.NPcoNP.NativePositiveBankDecode
