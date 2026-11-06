import Shared.Beeping.NPcoNP.NativeRow10ScannerEntry
import Shared.Beeping.NPcoNP.NativeRow10Operation

/-! Countdown, zero exit and either row-10 bank-operation branch. -/
namespace Shared.Beeping.NPcoNP.NativeRow10Countdown
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeRow8Cycles
open Shared.Beeping.NPcoNP.NativeRow8GraphCycles
open Shared.Beeping.NPcoNP.NativeRow8ZeroScan
open Shared.Beeping.NPcoNP.NativeRow10Operation
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- From a supplied prepared layout, the positive row-8 countdown and its
zero exit are followed by the actual row-10 zero or positive bank update.
The physical return from state 25 or 23 remains a separate obligation. -/
theorem countdown_then_row10 (n : Nat) (h separator : Int) (t : Int → Bool)
    (a b : Nat) (pre : List Nat) (v : Nat) (post : List Nat) (z : Nat)
    (rest : List Nat) (bank : Bank 12) (hlen : pre.length=4)
    (ready : Ready h separator t a b (pre++v::post) n z rest bank) :
    let values := a::(b+n)::pre
    let selected := cycleBanks n bank
    let result := target.system.step ⟨10,selected⟩
    let pos := separator+1+((encode values).length : Int)
    let more := rest++List.replicate n 0
    let tail := if v=0 then encode more ++ [false,false] else encode more ++ [true,false,false]
    let state : Fin 284 := if v=0 then 25 else 23
    let head := if v=0 then pos-1 else pos-2
    ∃ (k : Nat) (out : Int → Bool), n+3≤k ∧ CyclesGood n bank ∧
      target.system.step ⟨8,selected⟩=(⟨10,selected⟩,[]) ∧
      result.2=[] ∧ result.1.state=(if v=0 then 11 else 10) ∧
      Holds out (separator+1) (encode (arrayBank result.1.bank) ++ tail) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg state head out) k := by
  dsimp only
  let values := a::(b+n)::pre
  let selected := cycleBanks n bank
  let graphTail := post++[0,z]
  let more := rest++List.replicate n 0
  let pos := separator+1+((encode values).length : Int)
  have hvlen : values.length=6 := by simp [values,hlen]
  have start : Ready h separator t a b (pre++v::post) (0+n) z rest bank := by simpa using ready
  obtain ⟨_,_,_,_,_,rgraph,_⟩ :=
    finite_positive_cycles n h separator t a b (pre++v::post) 0 z rest bank start
  have harray : arrayBank selected=values ++ (v::graphTail) := by
    simpa [selected,values,graphTail,List.append_assoc] using rgraph.graph
  obtain ⟨k,mid,hk,hgood,hzero,hpath,hmark,h9,h10,hcontrol,hsep,hleft,hbank,hblank,hseg⟩ :=
    positive_cycles_then_enter_zero_scanner_full n h separator t a b (pre++v::post) z rest bank ready
  have hword : Holds mid (separator+1) (encode values ++ (encode (v::(graphTail++more)) ++ [false,false])) := by
    simpa [values,graphTail,more,bankWord,encode_append,encode,List.append_assoc] using hbank
  cases v with
  | zero =>
    have harray' : arrayBank selected=values ++ (0::graphTail) := harray
    have hword' : Holds mid (separator+1) (encode values ++ (encode (0::(graphTail++more)) ++ [false,false])) := hword
    obtain ⟨m,out,hm,hstate,hevent,hresult,hframe,hop⟩ := zero_operation h separator mid values graphTail more selected hvlen harray'
      ready.long hmark h9 h10 hcontrol hsep hword'
    have hall := segAdd machine _ _ _ k m hseg hop
    refine ⟨k+m,out,by omega,hgood,hzero,hevent,?_,?_,?_⟩
    · simpa using hstate
    · simpa [more] using hresult
    · simpa [pos] using hall
  | succ v =>
    have harray' : arrayBank selected=values ++ ((v+1)::graphTail) := by simpa using harray
    have hword' : Holds mid (separator+1) (encode values ++ (encode ((v+1)::(graphTail++more)) ++ [false,false])) := by simpa using hword
    obtain ⟨m,out,hm,hstate,hevent,hresult,hop⟩ := positive_operation h separator mid values graphTail more v selected hvlen harray'
      ready.long hmark h9 h10 hcontrol hsep hword'
    have hall := segAdd machine _ _ _ k m hseg hop
    refine ⟨k+m,out,by omega,hgood,hzero,hevent,?_,?_,?_⟩
    · simpa using hstate
    · simpa [more] using hresult
    · simpa [pos] using hall

#print axioms countdown_then_row10
end Shared.Beeping.NPcoNP.NativeRow10Countdown
