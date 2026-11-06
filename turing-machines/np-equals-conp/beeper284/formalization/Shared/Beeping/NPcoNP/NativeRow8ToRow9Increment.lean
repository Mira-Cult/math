import Shared.Beeping.NPcoNP.NativeRow8PositiveRedispatch
import Shared.Beeping.NPcoNP.Native275BankEntry
import Shared.Beeping.NPcoNP.NativeRow9Increment
import Shared.Beeping.NPcoNP.NativeRow9IncrementReturn
import Shared.Beeping.NPcoNP.NativeArrayGraphBank

/-! The positive row-8 physical step and the following row-9 increment,
with graph-bank readback in documented producer-array order. -/
namespace Shared.Beeping.NPcoNP.NativeRow8ToRow9Increment
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeRow8PositiveRedispatch
open Shared.Beeping.NPcoNP.Native275BankEntry
open Shared.Beeping.NPcoNP.NativeRow9Increment
open Shared.Beeping.NPcoNP.NativeRow9IncrementReturn
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.NativeFourthNextPath
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 20000000

/-- From a supplied positive row-8 physical layout, the table completes both
bank operations in a finite silent segment. The decoded bank is the result of
the two actual graph steps, in the documented array order. State 23 is an
intermediate physical boundary; its return and the next graph dispatch remain. -/
theorem positive_row8_then_row9 (h bound separator : Int) (t : Int → Bool)
    (a b : Nat) (prior : List Nat) (v z : Nat) (rest : List Nat) (graphBank : Bank 12)
    (hlen : prior.length=8)
    (hgraph : arrayBank graphBank=(a::b::prior) ++ [v+1,z])
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, bound≤q → t q=false)
    (bank : Holds t (separator+1)
      (encode (a::b::prior) ++ (encode ((v+1)::z::rest) ++ [false,false]))) :
    let first := (target.system.step ⟨8,graphBank⟩).1
    let second := (target.system.step ⟨9,first.bank⟩).1
    let tail := encode rest ++ [true,false]
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=23 ∧
      first.state=9 ∧ second.state=8 ∧
      (target.system.step ⟨8,graphBank⟩).2=[] ∧ (target.system.step ⟨9,first.bank⟩).2=[] ∧
      decode 12 (readCells e.tape (separator+1)
        (encode (arrayBank second.bank) ++ tail).length)=some (arrayBank second.bank,tail) ∧
      silentSegment machine (cfg 273 (h+8) t) e n := by
  dsimp only
  have hten : (a::b::prior).length=10 := by simp [hlen]
  obtain ⟨n,mid,hn,hpath,hparse,hbank,hleft,h9,h10,hrun,hsep,hseg⟩ :=
    positive_then_redispatch h bound separator t (a::b::prior) v (z::rest) hten hlong
      path left mark z1 z2 ones sep right bank
  let out := fillRange (setAt (h+8) mid) (h+11) (separator-1)
  let final := clearAt (h+8) out
  let pos := separator+1+((a+2 : Nat):Int)
  let bits := encode prior ++ (encode (v::z::rest) ++ [true,false,false])
  have hb : Holds final (separator+1) (block a ++ (block b ++ bits)) := by
    simpa [encode,bits,List.append_assoc] using hbank
  have hs := scan_to262 h separator final a b bits (by omega) h9 h10 hrun hsep hb
  let k := (separator-(h+11)).toNat
  have hs' : silentSegment machine (cfg 275 (h+9) final)
      (cfg 262 (pos-2) (clearAt pos final)) (k+a+7) := by simpa only [pos,k] using hs
  let suffix := prior ++ [v,z] ++ rest ++ [0]
  have hbankall : Holds final (separator+1) (encode (a::b::suffix) ++ [false]) := by
    simpa [suffix,encode_append,encode,block,List.append_assoc] using hbank
  have h8 : final (h+8)=false := by simp [final,clearAt]
  obtain ⟨e,he,hword,hframe,hinc⟩ := restore_then_increment h separator final a b suffix
    hlong h8 h9 h10 hrun hsep hbankall
  let ys := unaryBankPrefix (separator-(h+12)).toNat [a]
  let duration := (2*ys.length+7)+(b+2+(encode suffix).length)
  have hinc' : silentSegment machine (cfg 262 (pos-2) (clearAt pos final)) e duration := by
    simpa only [pos,ys,duration] using hinc
  have hgraphstep := row8_then9_array graphBank a b prior v z hlen hgraph
  obtain ⟨hfirst,hsecond,harr,hev1,hev2⟩ := hgraphstep
  have henc : encode ((a::(b+1)::prior) ++ [v,z]) ++ (encode rest ++ [true,false]) =
      encode (a::(b+1)::suffix) := by
    simp [suffix,encode_append,encode,block,List.append_assoc]
  have hout : Holds e.tape (separator+1)
      (encode (arrayBank (target.system.step ⟨9,(target.system.step ⟨8,graphBank⟩).1.bank⟩).1.bank) ++
        (encode rest ++ [true,false])) := by
    rw [harr,henc]
    exact hword
  have hlength : (arrayBank (target.system.step ⟨9,(target.system.step ⟨8,graphBank⟩).1.bank⟩).1.bank).length=12 := by
    simp [arrayBank]
  have hdecode := decode_encode
    (arrayBank (target.system.step ⟨9,(target.system.step ⟨8,graphBank⟩).1.bank⟩).1.bank)
    (encode rest ++ [true,false])
  rw [hlength] at hdecode
  have hread := read_of_holds e.tape (separator+1) _ hout
  rw [←hread] at hdecode
  have pre := segAdd machine _ _ _ n (k+a+7) hseg hs'
  have all := segAdd machine _ _ _ (n+(k+a+7)) duration pre hinc'
  exact ⟨n+(k+a+7)+duration,e,by omega,he,hfirst,hsecond,hev1,hev2,hdecode,all⟩

/-- The same two graph-bank updates, followed by the literal finite state-23
return to state 1. The subsequent carry and dispatch still require proof. -/
theorem positive_row8_then_row9_return (h bound separator : Int) (t : Int → Bool)
    (a b : Nat) (prior : List Nat) (v z : Nat) (rest : List Nat) (graphBank : Bank 12)
    (hlen : prior.length=8)
    (hgraph : arrayBank graphBank=(a::b::prior) ++ [v+1,z])
    (hlong : h+12≤separator) (path : Holds t (h-4) fifthPath)
    (left : ∀ q, q<h-4 → t q=false)
    (mark : t (h+7)=true) (z1 : t (h+8)=false) (z2 : t (h+9)=false)
    (ones : ∀ q, h+10≤q → q<separator → t q=true)
    (sep : t separator=false) (right : ∀ q, bound≤q → t q=false)
    (bank : Holds t (separator+1)
      (encode (a::b::prior) ++ (encode ((v+1)::z::rest) ++ [false,false]))) :
    let first := (target.system.step ⟨8,graphBank⟩).1
    let second := (target.system.step ⟨9,first.bank⟩).1
    let tail := encode rest ++ [true,false]
    ∃ (n : Nat) (e : Config 284), 0<n ∧ e.state=23 ∧
      first.state=9 ∧ second.state=8 ∧
      (target.system.step ⟨8,graphBank⟩).2=[] ∧ (target.system.step ⟨9,first.bank⟩).2=[] ∧
      decode 12 (readCells e.tape (separator+1)
        (encode (arrayBank second.bank) ++ tail).length)=some (arrayBank second.bank,tail) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 1 (h+7) e.tape) n := by
  dsimp only
  have hten : (a::b::prior).length=10 := by simp [hlen]
  obtain ⟨n,mid,hn,hpath,hparse,hbank,hleft,h9,h10,hrun,hsep,hseg⟩ :=
    positive_then_redispatch h bound separator t (a::b::prior) v (z::rest) hten hlong
      path left mark z1 z2 ones sep right bank
  let out := fillRange (setAt (h+8) mid) (h+11) (separator-1)
  let final := clearAt (h+8) out
  let pos := separator+1+((a+2 : Nat):Int)
  let bits := encode prior ++ (encode (v::z::rest) ++ [true,false,false])
  have hb : Holds final (separator+1) (block a ++ (block b ++ bits)) := by
    simpa [encode,bits,List.append_assoc] using hbank
  have hs := scan_to262 h separator final a b bits (by omega) h9 h10 hrun hsep hb
  let k := (separator-(h+11)).toNat
  have hs' : silentSegment machine (cfg 275 (h+9) final)
      (cfg 262 (pos-2) (clearAt pos final)) (k+a+7) := by simpa only [pos,k] using hs
  let suffix := prior ++ [v,z] ++ rest ++ [0]
  have hbankall : Holds final (separator+1) (encode (a::b::suffix) ++ [false]) := by
    simpa [suffix,encode_append,encode,block,List.append_assoc] using hbank
  have h8 : final (h+8)=false := by simp [final,clearAt]
  obtain ⟨m,e,hm,he,hword,hinc⟩ := increment_then_return h separator final a b suffix
    hlong h8 h9 h10 hrun hsep hbankall
  have hinc' : silentSegment machine (cfg 262 (pos-2) (clearAt pos final))
      (cfg 1 (h+7) e.tape) m := by
    simpa only [pos] using hinc
  have hgraphstep := row8_then9_array graphBank a b prior v z hlen hgraph
  obtain ⟨hfirst,hsecond,harr,hev1,hev2⟩ := hgraphstep
  have henc : encode ((a::(b+1)::prior) ++ [v,z]) ++ (encode rest ++ [true,false]) =
      encode (a::(b+1)::suffix) := by
    simp [suffix,encode_append,encode,block,List.append_assoc]
  have hout : Holds e.tape (separator+1)
      (encode (arrayBank (target.system.step ⟨9,(target.system.step ⟨8,graphBank⟩).1.bank⟩).1.bank) ++
        (encode rest ++ [true,false])) := by
    rw [harr,henc]
    exact hword
  have hlength : (arrayBank (target.system.step ⟨9,(target.system.step ⟨8,graphBank⟩).1.bank⟩).1.bank).length=12 := by
    simp [arrayBank]
  have hdecode := decode_encode
    (arrayBank (target.system.step ⟨9,(target.system.step ⟨8,graphBank⟩).1.bank⟩).1.bank)
    (encode rest ++ [true,false])
  rw [hlength] at hdecode
  have hread := read_of_holds e.tape (separator+1) _ hout
  rw [←hread] at hdecode
  have pre := segAdd machine _ _ _ n (k+a+7) hseg hs'
  have all := segAdd machine _ _ _ (n+(k+a+7)) m pre hinc'
  exact ⟨n+(k+a+7)+m,e,by omega,he,hfirst,hsecond,hev1,hev2,hdecode,all⟩

#print axioms positive_row8_then_row9_return
#print axioms positive_row8_then_row9
end Shared.Beeping.NPcoNP.NativeRow8ToRow9Increment
