import Shared.Beeping.NPcoNP.NativeRows8To11Frame
import Shared.Beeping.NPcoNP.NativeRow11Dispatch

/-! The row-11 control gap of length at least three reaches state 83.
The tape layout is supplied; no blank-start reachability is claimed. -/
namespace Shared.Beeping.NPcoNP.NativeRow11LongPrepare
open Shared.Beeping Shared.Beeping.Machines PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.Native54Prepare
open Shared.Beeping.NPcoNP.NativeRow11Dispatch
open Shared.Beeping.NPcoNP.NativeRows8To11Frame
open Shared.Beeping.NPcoNP.NativeRow10ZeroCarry
open Shared.Beeping.NPcoNP.NativeRow8Cycles
open Shared.Beeping.NPcoNP.NativeRow8GraphCycles
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- A row-11 path with at least three blank cells before the marker
reaches state 83 in a positive finite silent segment, preserving the suffix. -/
theorem long_gap_prepare (h separator : Int) (t : Int → Bool)
    (hlong : h+14≤separator)
    (path : Holds t (h-4) row11Path)
    (gap : ∀ q, h+6<q → q<separator-1 → t q=false)
    (marker : t (separator-1)=true) :
    let out := fillRange (setAt (h+10) t) (h+13) (separator-1)
    ∃ (k : Nat) (head : Int), 13<k ∧
      head=(if separator=h+14 then h+9 else separator-3) ∧
      out (h+10)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      (∀ q, q<h+10 → out q=t q) ∧
      silentSegment machine (cfg 93 (h-3) t) (cfg 83 head out) k := by
  dsimp only
  let r := (separator-(h+14)).toNat
  have hr : (r : Int)=separator-(h+14) := Int.toNat_of_nonneg (by omega)
  have h0 : t (h+10)=false := gap _ (by omega) (by omega)
  have h1 : t (h+10+1)=false := gap _ (by omega) (by omega)
  have h2 : t (h+10+2)=false := gap _ (by omega) (by omega)
  have hz : ∀ i : Nat, i<r → t (h+10+3+(i : Int))=false := by
    intro i hi
    apply gap <;> omega
  have hm : t (h+10+3+(r : Int))=true := by
    have he : h+10+3+(r : Int)=separator-1 := by omega
    rw [he]; exact marker
  have hs := zero_prepare_to83_exact (h+10) t r h0 h1 h2 hz hm
  let out := fillRange (setAt (h+10) t) (h+13) (separator-1)
  let duration := if r=0 then 7 else r+5
  let head := if r=0 then h+9 else separator-3
  have he : h+13+(r : Int)=separator-1 := by omega
  have hh : (if r=0 then h+10-1 else h+10+3+(r : Int)-2)=head := by
    dsimp [head]; split_ifs <;> omega
  have hh' : (if r=0 then h+10-1 else separator-1-2)=head := by
    dsimp [head]; split_ifs <;> omega
  have hs' : silentSegment machine (cfg 66 (h+10) t) (cfg 83 head out) duration := by
    simpa only [show h+10+3=h+13 by omega, he, hh, hh', out, duration] using hs
  have hright : ∀ q, separator≤q → out q=t q := by
    intro q hq
    have hn : ¬ (h+13≤q ∧ q<separator-1) := by omega
    have hne : q≠h+10 := by omega
    simp [out,fillRange,setAt,hn,hne]
  have hleft : ∀ q, q<h+10 → out q=t q := by
    intro q hq
    have hn : ¬ (h+13≤q ∧ q<separator-1) := by omega
    have hne : q≠h+10 := by omega
    simp [out,fillRange,setAt,hn,hne]
  have hhead : head=(if separator=h+14 then h+9 else separator-3) := by
    dsimp [head]
    split_ifs <;> omega
  have hmark : out (h+10)=true := by simp [out,fillRange,setAt]
  exact ⟨13+duration,head,by dsimp [duration]; split_ifs <;> omega,hhead,hmark,hright,hleft,
    segAdd machine _ _ _ 13 duration (dispatch_row11_path h t path) hs'⟩

/-- The long-gap preparation is reached from the supplied row-8 layout,
with the graph countdown facts and the complete encoded suffix retained. -/
theorem row8_to_long_prepare_bounded (n : Nat) (h separator : Int) (t : Int → Bool)
    (a b : Nat) (pre : List Nat) (v : Nat) (post : List Nat) (z : Nat)
    (rest : List Nat) (bank : Bank 12) (hlen : pre.length=4)
    (ready : NativeRow8Cycles.Ready h separator t a b (pre++v::post) n z rest bank)
    (hlong : h+14≤separator) :
    let selected := cycleBanks n bank
    let final := target.system.advance ⟨10,selected⟩ (v+1)
    ∃ (k : Nat) (head : Int) (out : Int → Bool), n+16<k ∧
      head=(if separator=h+14 then h+9 else separator-3) ∧
      Holds out (h-4) row11Path ∧ (∀ q, q<h-4 → out q=false) ∧ out (h+10)=true ∧
      out (h+11)=false ∧ out (h+12)=false ∧
      (∀ q, h+13≤q → q<separator-1 → out q=true) ∧
      out (separator-1)=true ∧ out separator=false ∧
      arrayBank final.bank=(a::(b+n)::pre) ++ (0::(post++[0,z])) ∧ CyclesGood n bank ∧
      target.system.step ⟨8,selected⟩=(⟨10,selected⟩,[]) ∧
      final.state=11 ∧
      Holds out (separator+1) (encode (arrayBank final.bank) ++
        (encode (rest++List.replicate n 0++List.replicate v 0) ++ [false,false])) ∧
      (∃ bound : Int, ∀ q, bound≤q → out q=false) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 83 head out) k := by
  dsimp only
  obtain ⟨k,mid,hk,hgood,hzero,hstate,_,hgraph,hpath,_,hl,hgap,hmark,hsep,hbank,⟨bound,hright⟩,hseg⟩ :=
    row8_then_row10_framed n h separator t a b pre v post z rest bank hlen ready
  obtain ⟨m,head,hm,hhead,hmarkOut,hframe,hleft,hnext⟩ := long_gap_prepare h separator mid hlong hpath hgap hmark
  let out := fillRange (setAt (h+10) mid) (h+13) (separator-1)
  have hb : Holds out (separator+1) (encode (arrayBank (target.system.advance ⟨10,cycleBanks n bank⟩ (v+1)).bank) ++
      (encode (rest++List.replicate n 0++List.replicate v 0) ++ [false,false])) := by
    apply holds_transport mid out _ _ hbank
    intro q hq _
    exact (hframe q (by omega)).symm
  have hp : Holds out (h-4) row11Path := by
    apply holds_transport mid out _ _ hpath
    intro q hq hq'
    have hc : q<h+10 := by simp [row11Path] at hq'; omega
    exact (hleft q hc).symm
  have hleft' : ∀ q, q<h-4 → out q=false := by
    intro q hq
    exact (hleft q (by omega)).trans (hl q hq)
  have hz11 : out (h+11)=false := by
    have hh := hgap (h+11) (by omega) (by omega)
    simpa [out,fillRange,setAt] using hh
  have hz12 : out (h+12)=false := by
    have hh := hgap (h+12) (by omega) (by omega)
    simpa [out,fillRange,setAt] using hh
  have hrun : ∀ q, h+13≤q → q<separator-1 → out q=true := by
    intro q hq hq'
    simp [out,fillRange, hq, hq']
  have hmarker : out (separator-1)=true := by
    have hn : ¬ (h+13≤separator-1 ∧ separator-1<separator-1) := by omega
    have hne : separator-1≠h+10 := by omega
    simpa [out,fillRange,setAt,hn,hne] using hmark
  have hzeroSep : out separator=false := (hframe separator (by omega)).trans hsep
  have hright' : ∀ q, max bound separator≤q → out q=false := by
    intro q hq
    have hqsep : separator≤q := le_trans (le_max_right _ _) hq
    have hqb : bound≤q := le_trans (le_max_left _ _) hq
    exact (hframe q hqsep).trans (hright q hqb)
  exact ⟨k+m,head,out,by omega,hhead,hp,hleft',hmarkOut,hz11,hz12,hrun,hmarker,hzeroSep,hgraph,hgood,hzero,hstate,hb,⟨max bound separator,hright'⟩,
    segAdd machine _ _ _ k m hseg hnext⟩

/-- Compatibility projection retaining the established frame interface. -/
theorem row8_to_long_prepare_full (n : Nat) (h separator : Int) (t : Int → Bool)
    (a b : Nat) (pre : List Nat) (v : Nat) (post : List Nat) (z : Nat)
    (rest : List Nat) (bank : Bank 12) (hlen : pre.length=4)
    (ready : NativeRow8Cycles.Ready h separator t a b (pre++v::post) n z rest bank)
    (hlong : h+14≤separator) :
    let selected := cycleBanks n bank
    let final := target.system.advance ⟨10,selected⟩ (v+1)
    ∃ (k : Nat) (head : Int) (out : Int → Bool), n+16<k ∧
      head=(if separator=h+14 then h+9 else separator-3) ∧
      Holds out (h-4) row11Path ∧ (∀ q, q<h-4 → out q=false) ∧ out (h+10)=true ∧
      out (h+11)=false ∧ out (h+12)=false ∧
      (∀ q, h+13≤q → q<separator-1 → out q=true) ∧
      out (separator-1)=true ∧ out separator=false ∧
      arrayBank final.bank=(a::(b+n)::pre) ++ (0::(post++[0,z])) ∧ CyclesGood n bank ∧
      target.system.step ⟨8,selected⟩=(⟨10,selected⟩,[]) ∧
      final.state=11 ∧
      Holds out (separator+1) (encode (arrayBank final.bank) ++
        (encode (rest++List.replicate n 0++List.replicate v 0) ++ [false,false])) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 83 head out) k := by
  obtain ⟨k,head,out,hk,hhead,hpath,hleft,h10,h11,h12,hrun,hmarker,hsep,hgraph,hgood,hzero,hstate,hbank,_,hseg⟩ :=
    row8_to_long_prepare_bounded n h separator t a b pre v post z rest bank hlen ready hlong
  exact ⟨k,head,out,hk,hhead,hpath,hleft,h10,h11,h12,hrun,hmarker,hsep,hgraph,hgood,hzero,hstate,hbank,hseg⟩

/-- Compatibility projection of the strengthened preparation interface. -/
theorem row8_to_long_prepare (n : Nat) (h separator : Int) (t : Int → Bool)
    (a b : Nat) (pre : List Nat) (v : Nat) (post : List Nat) (z : Nat)
    (rest : List Nat) (bank : Bank 12) (hlen : pre.length=4)
    (ready : NativeRow8Cycles.Ready h separator t a b (pre++v::post) n z rest bank)
    (hlong : h+14≤separator) :
    let selected := cycleBanks n bank
    let final := target.system.advance ⟨10,selected⟩ (v+1)
    ∃ (k : Nat) (head : Int) (out : Int → Bool), n+16<k ∧
      head=(if separator=h+14 then h+9 else separator-3) ∧
      Holds out (h-4) row11Path ∧ (∀ q, q<h-4 → out q=false) ∧ out (h+10)=true ∧
      out (h+11)=false ∧ out (h+12)=false ∧
      (∀ q, h+13≤q → q<separator-1 → out q=true) ∧ CyclesGood n bank ∧
      target.system.step ⟨8,selected⟩=(⟨10,selected⟩,[]) ∧
      final.state=11 ∧
      Holds out (separator+1) (encode (arrayBank final.bank) ++
        (encode (rest++List.replicate n 0++List.replicate v 0) ++ [false,false])) ∧
      silentSegment machine (cfg 273 (h+8) t) (cfg 83 head out) k := by
  obtain ⟨k,head,out,hk,hhead,hpath,hleft,h10,h11,h12,hrun,_,_,_,hgood,hzero,hstate,hbank,hseg⟩ :=
    row8_to_long_prepare_full n h separator t a b pre v post z rest bank hlen ready hlong
  exact ⟨k,head,out,hk,hhead,hpath,hleft,h10,h11,h12,hrun,hgood,hzero,hstate,hbank,hseg⟩

#print axioms long_gap_prepare
#print axioms row8_to_long_prepare_bounded
#print axioms row8_to_long_prepare_full
#print axioms row8_to_long_prepare
end Shared.Beeping.NPcoNP.NativeRow11LongPrepare
