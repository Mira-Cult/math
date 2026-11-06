import Shared.Beeping.NPcoNP.NativeRow8GraphCycles
import Shared.Beeping.NPcoNP.Native273ZeroNext
import Shared.Beeping.NPcoNP.NativeZeroGraphBank

/-! The supplied row-8 zero exit in producer-array bank order. -/
namespace Shared.Beeping.NPcoNP.NativeRow8ZeroExit
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.Coalescing284Map
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.NativeZeroGraphBank
open Shared.Beeping.NPcoNP.Native273ZeroNext
open Shared.Beeping.NPcoNP.NativeFifthZeroNextPath
open Shared.Beeping.NPcoNP.NativeRow8Cycles
open Shared.Beeping.NPcoNP.NativeRow8GraphCycles
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- Unlike the first two entries, producer-array entry 10 is suffix 10. -/
theorem bank10_zero_of_array (bank : Bank 12) (values : List Nat) (z : Nat)
    (hlen : values.length=10) (h : arrayBank bank=values ++ [0,z]) : bank 10=0 := by
  have he := congrArg (fun l : List Nat => l[10]?) h
  simpa [arrayBank,arrayToSuffix,List.getElem?_ofFn,List.getElem?_append,hlen] using he

/-- From a prepared zero value, graph row 8 silently selects row 10. The
literal table reaches state 64 in finite silent time, keeping the complete
bank suffix and its blank tail. -/
theorem zero_exit_full (h separator : Int) (t : Int → Bool)
    (a b : Nat) (prior : List Nat) (z : Nat) (rest : List Nat) (bank : Bank 12)
    (ready : Ready h separator t a b prior 0 z rest bank) :
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧
      Holds out (h-4) zeroNextPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.5.decnz",12) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, h+5<q → q<separator-1 → out q=false) ∧ out (separator-1)=true ∧
      (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (bankWord a b prior 0 z rest) ∧
      (∀ q, separator+1+((bankWord a b prior 0 z rest).length : Int)≤q → out q=false) ∧
      target.system.step ⟨8,bank⟩=(⟨10,bank⟩,[]) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 64 (h+8) out) k := by
  let values := a::b::prior
  let tail := encode (z::rest) ++ [false,false]
  let bound := separator+1+((bankWord a b prior 0 z rest).length : Int)
  have hlen : values.length=10 := by simp [values,ready.prior_length]
  have hword : Holds t (separator+1) (encode values ++ (block 0 ++ tail)) := by
    simpa [values,tail,bankWord,encode,List.append_assoc] using ready.word
  have hright : ∀ q, bound≤q → t q=false := ready.blank
  obtain ⟨k,out,hk,hpath,hparse,hframe,_,hleft,hgap,hmarker,hseg⟩ :=
    zero_to_next_dispatch_full h bound separator t values tail hlen ready.long ready.path
      ready.left ready.mark ready.zero8 ready.zero9 ready.control ready.sep hright hword
  have hbank : Holds out (separator+1) (bankWord a b prior 0 z rest) := by
    apply holds_transport t out _ _ ready.word
    intro q hq _
    exact (hframe q (by omega)).symm
  have hblank : ∀ q, separator+1+((bankWord a b prior 0 z rest).length : Int)≤q → out q=false := by
    intro q hq
    rw [hframe q (by omega)]
    exact ready.blank q hq
  have hreg : bank 10=0 := bank10_zero_of_array bank values z hlen ready.graph
  exact ⟨k,out,hk,hpath,hparse,hleft,hgap,hmarker,hframe,hbank,hblank,row8_zero bank hreg,hseg⟩

theorem zero_exit (h separator : Int) (t : Int → Bool)
    (a b : Nat) (prior : List Nat) (z : Nat) (rest : List Nat) (bank : Bank 12)
    (ready : Ready h separator t a b prior 0 z rest bank) :
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧
      Holds out (h-4) zeroNextPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.5.decnz",12) ∧
      (∀ q, q<h-4 → out q=false) ∧
      (∀ q, separator≤q → out q=t q) ∧
      Holds out (separator+1) (bankWord a b prior 0 z rest) ∧
      (∀ q, separator+1+((bankWord a b prior 0 z rest).length : Int)≤q → out q=false) ∧
      target.system.step ⟨8,bank⟩=(⟨10,bank⟩,[]) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 64 (h+8) out) k := by
  obtain ⟨k,out,hk,hpath,hparse,hleft,_,_,hframe,hbank,hblank,hgraph,hseg⟩ :=
    zero_exit_full h separator t a b prior z rest bank ready
  exact ⟨k,out,hk,hpath,hparse,hleft,hframe,hbank,hblank,hgraph,hseg⟩

/-- Any finite positive countdown, followed by its zero test, finishes
silently at the physical state-64 dispatcher for graph row 10. -/
theorem positive_cycles_then_zero (n : Nat) (h separator : Int) (t : Int → Bool)
    (a b : Nat) (prior : List Nat) (z : Nat) (rest : List Nat) (bank : Bank 12)
    (ready : Ready h separator t a b prior n z rest bank) :
    ∃ (k : Nat) (out : Int → Bool), n+1≤k ∧
      CyclesGood n bank ∧
      target.system.step ⟨8,cycleBanks n bank⟩=(⟨10,cycleBanks n bank⟩,[]) ∧
      Holds out (h-4) zeroNextPath ∧
      parseForward 52 out (h-4)=some ("3.$coalesced.5.decnz",12) ∧
      (∀ q, q<h-4 → out q=false) ∧
      Holds out (separator+1) (bankWord a (b+n) prior 0 z (rest++List.replicate n 0)) ∧
      (∀ q, separator+1+((bankWord a (b+n) prior 0 z (rest++List.replicate n 0)).length : Int)≤q → out q=false) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 64 (h+8) out) k := by
  have start : Ready h separator t a b prior (0+n) z rest bank := by simpa using ready
  obtain ⟨k,mid,hcount,hzero,hpos,rmid,hgood,hseg⟩ :=
    finite_positive_cycles_match n h separator t a b prior 0 z rest bank start
  obtain ⟨m,out,hm,hpath,hparse,hleft,hframe,hbank,hblank,hgraph,hseg'⟩ :=
    zero_exit h separator mid a (b+n) prior z (rest++List.replicate n 0) (cycleBanks n bank) rmid
  have all := segAdd machine _ _ _ k m hseg hseg'
  exact ⟨k+m,out,by omega,hgood,hgraph,hpath,hparse,hleft,hbank,hblank,all⟩

#print axioms bank10_zero_of_array
#print axioms zero_exit_full
#print axioms zero_exit
#print axioms positive_cycles_then_zero
end Shared.Beeping.NPcoNP.NativeRow8ZeroExit
