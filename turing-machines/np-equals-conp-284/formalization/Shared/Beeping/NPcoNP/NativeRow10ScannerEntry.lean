import Shared.Beeping.NPcoNP.NativeRow8ZeroScan
import Shared.Beeping.NPcoNP.Native280BankScan
import Shared.Beeping.NPcoNP.NativeRow10Array

/-! Connect the zero exit to the literal row-10 target-cell scan. -/
namespace Shared.Beeping.NPcoNP.NativeRow10ScannerEntry
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeRow8Cycles
open Shared.Beeping.NPcoNP.NativeRow8GraphCycles
open Shared.Beeping.NPcoNP.NativeRow8ZeroScan
open Shared.Beeping.NPcoNP.Native280BankScan
open Shared.Beeping.NPcoNP.NativeRow10Array
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- After the positive countdown and zero exit, state 280 scans the control
and six array blocks and temporarily clears the first one of array position 6.
The graph row-10 step itself is not yet implemented by this theorem. -/
theorem countdown_then_touch_row10 (n : Nat) (h separator : Int) (t : Int → Bool)
    (a b : Nat) (pre : List Nat) (v : Nat) (post : List Nat) (z : Nat)
    (rest : List Nat) (bank : Bank 12) (hlen : pre.length=4)
    (ready : Ready h separator t a b (pre++v::post) n z rest bank) :
    let values := a::(b+n)::pre
    let selected := cycleBanks n bank
    let pos := separator+1+((encode values).length : Int)
    ∃ (k : Nat) (mid : Int → Bool), n+3≤k ∧ CyclesGood n bank ∧
      target.system.step ⟨8,selected⟩=(⟨10,selected⟩,[]) ∧ selected 5=v ∧
      arrayBank selected=values ++ (v::(post++[0,z])) ∧
      Holds mid (separator+1) (bankWord a (b+n) (pre++v::post) 0 z (rest++List.replicate n 0)) ∧
      (∀ q, q≠pos → clearAt pos mid q=mid q) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 262 (pos-2) (clearAt pos mid)) k := by
  dsimp only
  let values := a::(b+n)::pre
  let selected := cycleBanks n bank
  let pos := separator+1+((encode values).length : Int)
  have start : Ready h separator t a b (pre++v::post) (0+n) z rest bank := by simpa using ready
  obtain ⟨_,_,_,_,_,rgraph,_⟩ :=
    finite_positive_cycles n h separator t a b (pre++v::post) 0 z rest bank start
  have harray : arrayBank selected=values ++ (v::(post++[0,z])) := by
    simpa [selected,values,List.append_assoc] using rgraph.graph
  have hv : selected 5=v := array_six selected values v (post++[0,z]) (by simp [values,hlen]) harray
  obtain ⟨k,mid,hk,hgood,hzero,hpath,hmark,h9,h10,hcontrol,hsep,hleft,hbank,hblank,hseg⟩ :=
    positive_cycles_then_enter_zero_scanner_full n h separator t a b (pre++v::post) z rest bank ready
  let tail := encode (post++[0,z]++(rest++List.replicate n 0)) ++ [false,false]
  have hword : Holds mid (separator+1) (encode values ++ (block v ++ tail)) := by
    simpa [values,tail,bankWord,encode_append,encode,List.append_assoc] using hbank
  obtain ⟨hframe,hscan⟩ := scan_to262 h separator mid values v tail (by simp [values,hlen])
    (by have := ready.long; omega) h9 h10 hcontrol hsep hword
  let duration := (separator-(h+11)).toNat+(encode values).length+5
  have hscan' : silentSegment machine (cfg 280 (h+9) mid) (cfg 262 (pos-2) (clearAt pos mid)) duration := by
    simpa only [pos,duration] using hscan
  have all := segAdd machine _ _ _ k duration hseg hscan'
  exact ⟨k+duration,mid,by dsimp [duration]; omega,hgood,hzero,hv,harray,hbank,hframe,all⟩

#print axioms countdown_then_touch_row10
end Shared.Beeping.NPcoNP.NativeRow10ScannerEntry
