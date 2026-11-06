import Shared.Beeping.NPcoNP.NativeRow10Countdown
import Shared.Beeping.NPcoNP.NativeRow10Next

/-! The row-8 countdown and row-10 operation through their next selector. -/
namespace Shared.Beeping.NPcoNP.NativeRow10CountdownNext
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeRow8Cycles
open Shared.Beeping.NPcoNP.NativeRow8GraphCycles
open Shared.Beeping.NPcoNP.NativeRow8ZeroScan
open Shared.Beeping.NPcoNP.NativeRow10Next
open Shared.Beeping.NPcoNP.NativeRow10ZeroCarry
open Shared.Beeping.NPcoNP.NativeRow10PositiveCarry
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- From a supplied prepared layout, the positive countdown, zero exit and
row-10 update finish silently at their actual next selector path. A positive
row-10 target selects `_continue.1`, whose further refinement is separate. -/
theorem countdown_then_row10_next (n : Nat) (h separator : Int) (t : Int → Bool)
    (a b : Nat) (pre : List Nat) (v : Nat) (post : List Nat) (z : Nat)
    (rest : List Nat) (bank : Bank 12) (hlen : pre.length=4)
    (ready : Ready h separator t a b (pre++v::post) n z rest bank) :
    let selected := cycleBanks n bank
    let result := target.system.step ⟨10,selected⟩
    let more := rest++List.replicate n 0
    let tail := if v=0 then encode more ++ [false,false] else encode more ++ [true,false,false]
    let nextPath := if v=0 then row11Path else positiveContinuationPath
    let nextOp := if v=0 then "3.$coalesced.6.decnz" else "_continue.1"
    let pathLength := if v=0 then 14 else 12
    ∃ (k : Nat) (out : Int → Bool), n+3≤k ∧ CyclesGood n bank ∧
      target.system.step ⟨8,selected⟩=(⟨10,selected⟩,[]) ∧
      result.2=[] ∧ result.1.state=(if v=0 then 11 else 10) ∧
      Holds out (h-4) nextPath ∧ parseForward 52 out (h-4)=some (nextOp,pathLength) ∧
      Holds out (separator+1) (encode (arrayBank result.1.bank) ++ tail) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 93 (h-3) out) k := by
  dsimp only
  let values := a::(b+n)::pre
  let selected := cycleBanks n bank
  let graphTail := post++[0,z]
  let more := rest++List.replicate n 0
  let bound := separator+1+((bankWord a (b+n) (pre++v::post) 0 z more).length : Int)
  have hvlen : values.length=6 := by simp [values,hlen]
  have start : Ready h separator t a b (pre++v::post) (0+n) z rest bank := by simpa using ready
  obtain ⟨_,_,_,_,_,rgraph,_⟩ :=
    finite_positive_cycles n h separator t a b (pre++v::post) 0 z rest bank start
  have harray : arrayBank selected=values ++ (v::graphTail) := by
    simpa [selected,values,graphTail,List.append_assoc] using rgraph.graph
  obtain ⟨k,mid,hk,hgood,hzero,hpath,hmark,h9,h10,hcontrol,hsep,hleft,hbank,hblank,hseg⟩ :=
    positive_cycles_then_enter_zero_scanner_full n h separator t a b (pre++v::post) z rest bank ready
  have hright : ∀ q, bound≤q → mid q=false := by simpa only [bound,more] using hblank
  have hword : Holds mid (separator+1) (encode values ++ (encode (v::(graphTail++more)) ++ [false,false])) := by
    simpa [values,graphTail,more,bankWord,encode_append,encode,List.append_assoc] using hbank
  cases v with
  | zero =>
    have harray' : arrayBank selected=values ++ (0::graphTail) := harray
    have hword' : Holds mid (separator+1) (encode values ++ (encode (0::(graphTail++more)) ++ [false,false])) := hword
    obtain ⟨m,out,hm,hstate,hevent,hnext,hparse,hresult,hframe,hop⟩ :=
      zero_operation_next h bound separator mid values graphTail more selected hvlen harray'
        ready.long hpath hleft hmark h9 h10 hcontrol hsep hright hword'
    have hall := segAdd machine _ _ _ k m hseg hop
    refine ⟨k+m,out,by omega,hgood,hzero,hevent,?_,?_,?_,?_,hall⟩
    · simpa using hstate
    · simpa using hnext
    · simpa using hparse
    · simpa [more] using hresult
  | succ v =>
    have harray' : arrayBank selected=values ++ ((v+1)::graphTail) := by simpa using harray
    have hword' : Holds mid (separator+1) (encode values ++ (encode ((v+1)::(graphTail++more)) ++ [false,false])) := by simpa using hword
    obtain ⟨m,out,hm,hstate,hevent,hnext,hparse,hresult,hop⟩ :=
      positive_operation_next h bound separator mid values graphTail more v selected hvlen harray'
        ready.long hpath hleft hmark h9 h10 hcontrol hsep hright hword'
    have hall := segAdd machine _ _ _ k m hseg hop
    refine ⟨k+m,out,by omega,hgood,hzero,hevent,?_,?_,?_,?_,hall⟩
    · simpa using hstate
    · simpa using hnext
    · simpa using hparse
    · simpa [more] using hresult

#print axioms countdown_then_row10_next
end Shared.Beeping.NPcoNP.NativeRow10CountdownNext
