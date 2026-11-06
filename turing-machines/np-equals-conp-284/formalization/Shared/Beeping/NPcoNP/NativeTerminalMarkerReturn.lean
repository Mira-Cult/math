import Shared.Beeping.NPcoNP.NativeTerminalMarkerFill
import Shared.Beeping.NPcoNP.NativeVariableMarkerReturn
import Shared.Beeping.NPcoNP.NativeHalfTapeScan

/-! Exact return from the marker-at-head fill, including its blank delimiters. -/
namespace Shared.Beeping.NPcoNP.NativeTerminalMarkerReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeMarkerExtraZeroReturn
open Shared.Beeping.NPcoNP.NativeVariableMarkerReturn
open Shared.Beeping.NPcoNP.NativeFirstDispatch
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeTerminalMarkerFill
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000

/-- The marker-at-head path fills a bounded corridor and returns to the same
selector head, preserving the left ray and setting the event-trigger cell. -/
theorem terminal_marker_roundtrip (t : Int → Bool) (a : Int) (r : Nat) (hr : 2≤r)
    (blank : ∀ q, q<a-2 → t q=false) (left0 : t (a-2)=false)
    (left1 : t (a-1)=true) (mark : t a=true)
    (zeros : ∀ q, a<q → q<a+6+(r : Int) → t q=false)
    (stop : t (a+6+(r : Int))=true) :
    let out := fillRange (setAt (a+3) t) (a+6) (a+6+(r : Int))
    silentSegment machine (cfg 93 a t) (cfg 93 a out) (2*r+36) ∧
      out a=true ∧ out (a+1)=false ∧ out (a+2)=false ∧ out (a+3)=true := by
  dsimp only
  let out := fillRange (setAt (a+3) t) (a+6) (a+6+(r : Int))
  have hfill := terminal_marker_fill t a r (by omega) mark zeros stop
  have before : ∀ q, q<a+6 → q≠a+3 → out q=t q := by
    intro q hq hne
    simp [out,fillRange,setAt,show ¬a+6≤q by omega,hne]
  have ba : out a=true := (before _ (by omega) (by omega)).trans mark
  have b1 : out (a+1)=false := (before _ (by omega) (by omega)).trans (zeros _ (by omega) (by omega))
  have b2 : out (a+2)=false := (before _ (by omega) (by omega)).trans (zeros _ (by omega) (by omega))
  have b3 : out (a+3)=true := by simp [out,fillRange,setAt,show ¬a+6≤a+3 by omega]
  have b4 : out (a+4)=false := (before _ (by omega) (by omega)).trans (zeros _ (by omega) (by omega))
  have b5 : out (a+5)=false := (before _ (by omega) (by omega)).trans (zeros _ (by omega) (by omega))
  have bl0 : out (a-2)=false := (before _ (by omega) (by omega)).trans left0
  have bl1 : out (a-1)=true := (before _ (by omega) (by omega)).trans left1
  have bray : ∀ q, q<a-2 → out q=false := by
    intro q hq; exact (before _ (by omega) (by omega)).trans (blank q hq)
  let bits : List Bool := [false,true,true,false,false,true,false,false]
  have hpref : Holds out (a-2) bits := by
    dsimp [bits]
    simp only [Holds]
    refine ⟨bl0,?_,?_,?_,?_,?_,?_,?_,trivial⟩ <;>
      first | simpa only [show a-2+1=a-1 by omega] using bl1
            | simpa only [show a-2+1+1=a by omega] using ba
            | simpa only [show a-2+1+1+1=a+1 by omega] using b1
            | simpa only [show a-2+1+1+1+1=a+2 by omega] using b2
            | simpa only [show a-2+1+1+1+1+1=a+3 by omega] using b3
            | simpa only [show a-2+1+1+1+1+1+1=a+4 by omega] using b4
            | simpa only [show a-2+1+1+1+1+1+1+1=a+5 by omega] using b5
  have hrun : Holds out (a+6) (List.replicate (r-1) true) := by
    apply holds_of_get
    intro i hi
    have hi' : i<r-1 := by simpa using hi
    simp only [List.getElem_replicate]
    have hp : a+6≤a+6+(i : Int) ∧ a+6+(i : Int)<a+6+(r : Int) := by omega
    simp [out,fillRange,hp]
  let word := List.replicate 9 false ++ bits ++ List.replicate (r-1) true
  have hblanks : Holds out (a-11) (List.replicate 9 false) := by
    apply holds_of_get
    intro i hi
    have hi' : i<9 := by simpa using hi
    simp only [List.getElem_replicate]
    exact bray _ (by omega)
  have hbody : Holds out (a-2) (bits ++ List.replicate (r-1) true) := by
    apply holds_append_intro out (a-2) bits _ hpref
    have hp : a-2+((bits.length : Nat):Int)=a+6 := by simp [bits]; omega
    simpa only [hp] using hrun
  have hw : Holds out (a-11) word := by
    refine holds_append_intro out (a-11) (List.replicate 9 false)
      (bits ++ List.replicate (r-1) true) hblanks ?_
    have hp : a-11+((List.replicate 9 false).length : Int)=a-2 := by simp; omega
    rw [hp]
    exact hbody
  let counts := [r-1,0,1,0,2] ++ List.replicate 9 0
  have hrev : word.reverse=blocks counts := by
    simp [word,bits,counts,blocks_append,blocks_zeroes,blocks,List.reverse_append,
      List.reverse_replicate,List.append_assoc]
  have hlen : word.length=r+16 := by dsimp [word,bits]; simp; omega
  have hd := holds_reverse out (a-11) word hw
  rw [hrev,hlen] at hd
  have hcounts : counts.length=14 := by simp [counts]
  have hchain := (chain_blocks chain83 counts _ out [] hcounts (by simpa using hd)).2
  have hb : (blocks counts).length=r+16 := by
    have hh := congrArg List.length hrev
    simpa only [List.length_reverse,hlen] using hh.symm
  rw [hb] at hchain
  have hchain' : silentSegment machine (cfg 83 (a+6+(r : Int)-2) out)
      (cfg 92 (a-12) out) (r+16) := by
    have hstart : a-11+((r+16 : Nat):Int)-1=a+6+(r : Int)-2 := by push_cast; omega
    have hend : a-11+((r+16 : Nat):Int)-1-((r+16 : Nat):Int)=a-12 := by omega
    simp only [Nat.cast_add, Nat.cast_ofNat] at hchain hstart hend
    rw [hend] at hchain
    simpa only [hstart] using hchain
  have h92 := scan92_exact 11 (a-12) out (by
    intro i hi
    by_cases he : i=10
    · subst i; simpa only [show a-12+((10 : Nat):Int)=a-2 by omega] using bl0
    · exact bray _ (by omega)) (by simpa only [show a-12+((11 : Nat):Int)=a-1 by omega] using bl1)
  have h92' : silentSegment machine (cfg 92 (a-12) out) (cfg 93 a out) 12 := by
    simpa only [show a-12+((11 : Nat):Int)+1=a by omega] using h92
  have hall := segAdd machine _ _ _ (r+8) (r+16+12) hfill
    (segAdd machine _ _ _ (r+16) 12 hchain' h92')
  have hn : r+8+(r+16+12)=2*r+36 := by omega
  exact ⟨by simpa only [out,hn] using hall,ba,b1,b2,b3⟩

#print axioms terminal_marker_roundtrip
end Shared.Beeping.NPcoNP.NativeTerminalMarkerReturn
