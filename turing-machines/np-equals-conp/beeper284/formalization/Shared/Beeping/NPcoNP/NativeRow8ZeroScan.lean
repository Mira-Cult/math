import Shared.Beeping.NPcoNP.NativeRow8ZeroExit
import Shared.Beeping.NPcoNP.Native64ReturnTo280

/-! Positive countdown and zero exit through literal state-64 preparation. -/
namespace Shared.Beeping.NPcoNP.NativeRow8ZeroScan
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeFifthZeroNextPath
open Shared.Beeping.NPcoNP.NativeRow8Cycles
open Shared.Beeping.NPcoNP.NativeRow8GraphCycles
open Shared.Beeping.NPcoNP.NativeRow8ZeroExit
open Shared.Beeping.NPcoNP.Native64ReturnTo280
open Shared.Beeping.NPcoNP.Grammar284ForwardParser
open Shared.Beeping.NPcoNP.Parent290Coalesced
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- The complete positive countdown, its zero branch, and the state-64
preparation finish silently. The physical row-10 scanner is entered; its bank operation remains separate. -/
theorem positive_cycles_then_enter_zero_scanner_full (n : Nat) (h separator : Int) (t : Int → Bool)
    (a b : Nat) (prior : List Nat) (z : Nat) (rest : List Nat) (bank : Bank 12)
    (ready : Ready h separator t a b prior n z rest bank) :
    ∃ (k : Nat) (out : Int → Bool), n+2≤k ∧
      CyclesGood n bank ∧
      target.system.step ⟨8,cycleBanks n bank⟩=(⟨10,cycleBanks n bank⟩,[]) ∧
      Holds out (h-4) zeroNextPath ∧ out (h+8)=true ∧
      out (h+9)=false ∧ out (h+10)=false ∧
      (∀ q, h+11≤q → q<separator → out q=true) ∧ out separator=false ∧
      (∀ q, q<h-4 → out q=false) ∧
      Holds out (separator+1) (bankWord a (b+n) prior 0 z (rest++List.replicate n 0)) ∧
      (∀ q, separator+1+((bankWord a (b+n) prior 0 z (rest++List.replicate n 0)).length : Int)≤q → out q=false) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 280 (h+9) out) k := by
  have start : Ready h separator t a b prior (0+n) z rest bank := by simpa using ready
  obtain ⟨k,mid,hcount,hzero,hpos,rmid,hgood,hseg⟩ :=
    finite_positive_cycles_match n h separator t a b prior 0 z rest bank start
  obtain ⟨m,gapTape,hm,hpath,hparse,hleft,hgap,hmarker,hframe,hbank,hblank,hgraph,hseg'⟩ :=
    zero_exit_full h separator mid a (b+n) prior z (rest++List.replicate n 0) (cycleBanks n bank) rmid
  let out := fillRange (setAt (h+8) gapTape) (h+11) (separator-1)
  obtain ⟨p,hp,hpath',hleft',hmark,h9,h10,hcontrol,hframe',hseg''⟩ :=
    prepare_and_enter_full h separator gapTape ready.long hpath hleft hgap hmarker
  have hbank' : Holds out (separator+1) (bankWord a (b+n) prior 0 z (rest++List.replicate n 0)) := by
    apply holds_transport gapTape out _ _ hbank
    intro q hq _
    exact (hframe' q (by omega)).symm
  have hblank' : ∀ q, separator+1+((bankWord a (b+n) prior 0 z (rest++List.replicate n 0)).length : Int)≤q → out q=false := by
    intro q hq
    change (fillRange (setAt (h+8) gapTape) (h+11) (separator-1)) q=false
    rw [hframe' q (by omega)]
    exact hblank q hq
  have hsep' : out separator=false := by
    change (fillRange (setAt (h+8) gapTape) (h+11) (separator-1)) separator=false
    rw [hframe' separator (by omega),hframe separator (by omega)]
    exact rmid.sep
  have first := segAdd machine _ _ _ k m hseg hseg'
  have all := segAdd machine _ _ _ (k+m) p first hseg''
  exact ⟨k+m+p,out,by omega,hgood,hgraph,hpath',hmark,h9,h10,hcontrol,hsep',hleft',hbank',hblank',all⟩

theorem positive_cycles_then_enter_zero_scanner (n : Nat) (h separator : Int) (t : Int → Bool)
    (a b : Nat) (prior : List Nat) (z : Nat) (rest : List Nat) (bank : Bank 12)
    (ready : Ready h separator t a b prior n z rest bank) :
    ∃ (k : Nat) (out : Int → Bool), n+2≤k ∧
      CyclesGood n bank ∧
      target.system.step ⟨8,cycleBanks n bank⟩=(⟨10,cycleBanks n bank⟩,[]) ∧
      Holds out (h-4) zeroNextPath ∧ out (h+8)=true ∧
      (∀ q, q<h-4 → out q=false) ∧
      Holds out (separator+1) (bankWord a (b+n) prior 0 z (rest++List.replicate n 0)) ∧
      (∀ q, separator+1+((bankWord a (b+n) prior 0 z (rest++List.replicate n 0)).length : Int)≤q → out q=false) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 280 (h+9) out) k := by
  obtain ⟨k,out,hk,hgood,hgraph,hpath,hmark,_,_,_,_,hleft,hbank,hblank,hseg⟩ :=
    positive_cycles_then_enter_zero_scanner_full n h separator t a b prior z rest bank ready
  exact ⟨k,out,hk,hgood,hgraph,hpath,hmark,hleft,hbank,hblank,hseg⟩

#print axioms positive_cycles_then_enter_zero_scanner_full
#print axioms positive_cycles_then_enter_zero_scanner
end Shared.Beeping.NPcoNP.NativeRow8ZeroScan
