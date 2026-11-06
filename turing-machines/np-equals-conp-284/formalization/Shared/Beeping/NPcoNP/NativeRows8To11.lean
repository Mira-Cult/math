import Shared.Beeping.NPcoNP.NativeRow10CountdownFull
import Shared.Beeping.NPcoNP.NativeRow10CountdownNext

/-! Composition of the supplied physical row-8 and row-10 countdowns. -/
namespace Shared.Beeping.NPcoNP.NativeRows8To11
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeRow8Cycles
open Shared.Beeping.NPcoNP.NativeRow8GraphCycles
open Shared.Beeping.NPcoNP.NativeRow8ZeroScan
open Shared.Beeping.NPcoNP.NativeRow10CountdownFull
open Shared.Beeping.NPcoNP.NativeRow10ZeroCarry
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- Two explicit zero cells followed by a blank tail yield a blank tail from
immediately after the encoded bank. -/
theorem blank_after_word (t : Int → Bool) (start : Int) (bits : List Bool)
    (word : Holds t start (bits ++ [false,false]))
    (tail : ∀ q, start+((bits ++ [false,false]).length : Int)≤q → t q=false) :
    ∀ q, start+(bits.length : Int)≤q → t q=false := by
  have hw := holds_append_tail t start bits [false,false] word
  intro q hq
  by_cases h0 : q=start+(bits.length : Int)
  · simpa only [h0] using hw.1
  by_cases h1 : q=start+(bits.length : Int)+1
  · simpa only [h1] using hw.2.1
  · apply tail
    simp only [List.length_append,List.length_cons,List.length_nil]
    push_cast
    omega

/-- Under the row-8 prepared-layout hypothesis, both finite countdowns and
both zero exits complete silently at the row-11 selector. -/
theorem row8_then_row10_countdowns (n : Nat) (h separator : Int) (t : Int → Bool)
    (a b : Nat) (pre : List Nat) (v : Nat) (post : List Nat) (z : Nat)
    (rest : List Nat) (bank : Bank 12) (hlen : pre.length=4)
    (ready : NativeRow8Cycles.Ready h separator t a b (pre++v::post) n z rest bank) :
    let selected := cycleBanks n bank
    ∃ (k : Nat) (out : Int → Bool), n+3≤k ∧ CyclesGood n bank ∧
      target.system.step ⟨8,selected⟩=(⟨10,selected⟩,[]) ∧
      (target.system.advance ⟨10,selected⟩ (v+1)).state=11 ∧
      target.system.wordFrom ⟨10,selected⟩ (v+1)=[] ∧
      Holds out (h-4) row11Path ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.6.decnz",14) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 93 (h-3) out) k := by
  dsimp only
  let values := a::(b+n)::pre
  let selected := cycleBanks n bank
  let graphTail := post++[0,z]
  let more := rest++List.replicate n 0
  let bits := encode values ++ encode (v::(graphTail++more))
  have hvlen : values.length=6 := by simp [values,hlen]
  have start : NativeRow8Cycles.Ready h separator t a b (pre++v::post) (0+n) z rest bank := by simpa using ready
  obtain ⟨_,_,_,_,_,rgraph,_⟩ :=
    finite_positive_cycles n h separator t a b (pre++v::post) 0 z rest bank start
  have harray : arrayBank selected=values ++ (v::graphTail) := by
    simpa [selected,values,graphTail,List.append_assoc] using rgraph.graph
  obtain ⟨k,mid,hk,hgood,hzero,hpath,hmark,h9,h10,hcontrol,hsep,hleft,hbank,hblank,hseg⟩ :=
    positive_cycles_then_enter_zero_scanner_full n h separator t a b (pre++v::post) z rest bank ready
  have hword : Holds mid (separator+1) (bits ++ [false,false]) := by
    simpa [bits,values,graphTail,more,bankWord,encode_append,encode,List.append_assoc] using hbank
  have htail : ∀ q, separator+1+((bits ++ [false,false]).length : Int)≤q → mid q=false := by
    simpa [bits,values,graphTail,more,bankWord,encode_append,encode,List.append_assoc] using hblank
  have htail' : ∀ q, bankEnd separator values v graphTail more≤q → mid q=false := by
    simpa [bankEnd,bits] using blank_after_word mid (separator+1) bits hword htail
  have r10 : NativeRow10CountdownFull.Ready h separator mid values graphTail more v selected :=
    ⟨hvlen,harray,ready.long,hpath,hleft,hmark,h9,h10,hcontrol,hsep,htail',by simpa [bits,List.append_assoc] using hword⟩
  obtain ⟨m,out,hm,hs,he,hnext,hparse,hop⟩ :=
    countdown_to_row11 v h separator mid values graphTail more selected r10
  exact ⟨k+m,out,by omega,hgood,hzero,hs,he,hnext,hparse,segAdd machine _ _ _ k m hseg hop⟩

#print axioms blank_after_word
#print axioms row8_then_row10_countdowns
end Shared.Beeping.NPcoNP.NativeRows8To11
