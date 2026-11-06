import Shared.Beeping.NPcoNP.NativeRow8ToRow9Prepared

/-! A blank bank suffix is preserved through a positive row-8/row-9 cycle. -/
namespace Shared.Beeping.NPcoNP.NativeRow8ToRow9BlankTail
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeFourthNextPath
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.NativeRow8ToRow9Prepared
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

theorem positive_row8_then_row9_blank_tail (h bound separator : Int) (t : Int → Bool)
    (a b : Nat) (prior : List Nat) (v z : Nat) (rest : List Nat) (graphBank : Bank 12)
    (hlen : prior.length=8)
    (hgraph : arrayBank graphBank=(a::b::prior) ++ [v+1,z])
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, bound≤q → t q=false)
    (bank : Holds t (separator+1)
      (encode (a::b::prior) ++ (encode ((v+1)::z::rest) ++ [false,false])))
    (blank : ∀ q, separator+1+(((encode (a::b::prior) ++ (encode ((v+1)::z::rest) ++ [false,false])).length : Nat):Int)≤q → t q=false) :
    let first := (target.system.step ⟨8,graphBank⟩).1
    let second := (target.system.step ⟨9,first.bank⟩).1
    let tail := encode rest ++ [true,false]
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧ Holds out (h-4) fifthPath ∧
      (∀ q, q<h-4 → out q=false) ∧ out (h+7)=true ∧
      (out (h+8)=false ∧ out (h+9)=false) ∧
      (∀ q, h+10≤q → q<separator → out q=true) ∧ out separator=false ∧
      (∃ endBound, ∀ q, endBound≤q → out q=false) ∧
      (∀ q, separator+1+(((encode (a::b::prior) ++ (encode ((v+1)::z::rest) ++ [false,false])).length : Nat):Int)≤q → out q=t q) ∧
      Holds out (separator+1) ((encode (arrayBank second.bank) ++ tail) ++ [false,false]) ∧
      first.state=9 ∧ second.state=8 ∧
      (target.system.step ⟨8,graphBank⟩).2=[] ∧ (target.system.step ⟨9,first.bank⟩).2=[] ∧
      decode 12 (readCells out (separator+1)
        (encode (arrayBank second.bank) ++ tail).length)=some (arrayBank second.bank,tail) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 273 (h+8) out) n := by
  dsimp only
  obtain ⟨n,out,hn,hpath,hleft,h7,h89,hones,hsep,hblank,hframe,hbank,
    hfirst,hsecond,hev1,hev2,hdecode,hseg⟩ :=
    positive_row8_then_row9_prepared_suffix_frame h bound separator t a b prior v z rest graphBank
      hlen hgraph hlong path left mark z1 z2 ones sep right bank
  let resultBank := (target.system.step ⟨9,(target.system.step ⟨8,graphBank⟩).1.bank⟩).1.bank
  let word := encode (arrayBank resultBank) ++ (encode rest ++ [true,false])
  let original := encode (a::b::prior) ++ (encode ((v+1)::z::rest) ++ [false,false])
  have harr := (row8_then9_array graphBank a b prior v z hlen hgraph).2.2.1
  have hlenWord : word.length=original.length := by
    dsimp [word,original,resultBank]
    rw [harr]
    simp [encode_append,encode,block_length]
    omega
  have hword : Holds out (separator+1) word := hbank
  have htail : Holds out (separator+1+(word.length : Int)) [false,false] := by
    rw [hlenWord]
    change out (separator+1+(original.length : Int))=false ∧
      out (separator+1+(original.length : Int)+1)=false ∧ True
    constructor
    · rw [hframe _ (by dsimp [original]; omega)]
      exact blank _ (by dsimp [original]; omega)
    constructor
    · rw [hframe _ (by dsimp [original]; omega)]
      exact blank _ (by dsimp [original]; omega)
    · trivial
  have hbank' := holds_append_intro out (separator+1) word [false,false] hword htail
  exact ⟨n,out,hn,hpath,hleft,h7,h89,hones,hsep,hblank,hframe,hbank',
    hfirst,hsecond,hev1,hev2,hdecode,hseg⟩

#print axioms positive_row8_then_row9_blank_tail
end Shared.Beeping.NPcoNP.NativeRow8ToRow9BlankTail
