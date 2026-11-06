import Shared.Beeping.NPcoNP.NativeUnit261CycleExact83
import Shared.Beeping.NPcoNP.NativeTerminalUnitCycle
import Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch

/-! Connect the unit increment macro to the terminal-marker selector.
The input tape layout is explicit; this is not an all-run invariant. -/
namespace Shared.Beeping.NPcoNP.NativeUnitTerminalBridgeExact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
open Shared.Beeping.NPcoNP.NativeUnit261Return1
open Shared.Beeping.NPcoNP.NativeUnit261CycleExact83
open Shared.Beeping.NPcoNP.NativeTerminalUnitCycle
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

/-- With the terminal selector window and a run of at least two ones,
the 261 increment returns to state 83 twice in exactly counted steps. The second return passes
state 10 with a proved marker and retains the incremented bank. -/
theorem dispatch_through_terminal_exact (r v z : Nat) (rest : List Nat)
    (h a : Int) (t : Int → Bool)
    (hr : 1<r) (hpre : t (h-1)=false) (hone : t h=true) (hzero : t (h+1)=false)
    (scanword : Holds t (h+2) (List.replicate r true ++ [false]))
    (bank : Holds t (h+2+(r : Int)+1) (encode (v::rest) ++ [false]))
    (hl : (List.replicate z 0 ++ [1]).length=14)
    (hpos : a+((2*z : Nat):Int)+3=h-1)
    (window : Holds t a (markerWindow (List.replicate z 0 ++ [1])))
    (left : t (a-1)=true) :
    let base := h+2+(r : Int)+1
    let values := (v+1)::rest
    ∃ mid : Config 284, mid.state=23 ∧
      silentSegment machine (cfg 261 h t) mid (r+v+6+(encode rest).length) ∧
      let u := put (put mid.tape (h-1) true) (h+2) false
      let out := put (clearRange u (h+3) (h+2+(r : Int))) (h+1+(r : Int)) true
      let final := fillRange (setAt h out) (h+2) (h+1+(r : Int))
      Holds final base (encode values) ∧
      (∀ q, base≤q → final q=mid.tape q) ∧
      silentSegment machine mid (cfg 83 (h+(r : Int)-1) final)
        ((encode values).length+r+2+(2*r+7)+(4*z+(r-1)+12)) := by
  dsimp only
  let base := h+2+(r : Int)+1
  let values := (v+1)::rest
  let xs := List.replicate z 0 ++ [1]
  obtain ⟨mid,hstate,hbank,hfirst,_houtbank,hright,h83⟩ :=
    dispatch_increment_to83_exact r v rest h t (by omega) hpre hone hzero scanword bank
  obtain ⟨other,_hs,_hb,_hm,hframe,hfirst',_hret⟩ :=
    dispatch_increment_return1 r v rest h t (by omega) hone hzero scanword bank
  have he : mid=other := hfirst.1.symm.trans hfirst'.1
  subst other
  let u := put (put mid.tape (h-1) true) (h+2) false
  let out := put (clearRange u (h+3) (h+2+(r : Int))) (h+1+(r : Int)) true
  have hprefix : ∀ q, q<h-1 → out q=t q := by
    intro q hq
    change put (clearRange u (h+3) (h+2+(r : Int))) (h+1+(r : Int)) true q=t q
    rw [put_other _ _ _ _ (by omega)]
    change (if h+3≤q ∧ q<h+2+(r : Int) then false else u q)=t q
    rw [if_neg (by omega)]
    change put (put mid.tape (h-1) true) (h+2) false q=t q
    rw [put_other _ _ _ _ (by omega),put_other _ _ _ _ (by omega)]
    exact hframe q (by omega) (Or.inl (by omega))
  have hwindow : Holds out a (markerWindow xs) := by
    apply holds_transport t out a (markerWindow xs) window
    intro q hq hq'
    symm
    apply hprefix
    have hlen : (markerWindow xs).length=2*z+3 := by
      simp [xs,markerWindow_length,encode_append,encode,block_length,zeros_length]
    rw [hlen] at hq'
    omega
  have hleft : out (a-1)=true := by
    rw [hprefix _ (by omega)]
    exact left
  have hmarker : out (a+((2*z : Nat):Int)+3)=true := by
    have hp : a+((2*z : Nat):Int)+3=h-1 := hpos
    rw [hp]
    dsimp [out,u]
    rw [put_other _ _ _ _ (by omega)]
    change (if h+3≤h-1 ∧ h-1<h+2+(r : Int) then false else
      put (put mid.tape (h-1) true) (h+2) false (h-1))=true
    rw [if_neg (by omega),put_other _ _ _ _ (by omega)]
    simp [put]
  have h0 : out (a+((2*z : Nat):Int)+4)=false := by
    have hp : a+((2*z : Nat):Int)+4=h := by omega
    rw [hp]
    dsimp [out,u]
    rw [put_other _ _ _ _ (by omega)]
    change (if h+3≤h ∧ h<h+2+(r : Int) then false else
      put (put mid.tape (h-1) true) (h+2) false h)=false
    rw [if_neg (by omega),put_other _ _ _ _ (by omega),put_other _ _ _ _ (by omega)]
    exact _hm
  have h1 : out (a+((2*z : Nat):Int)+5)=false := by
    have hp : a+((2*z : Nat):Int)+5=h+1 := by omega
    rw [hp]
    dsimp [out,u]
    rw [put_other _ _ _ _ (by omega)]
    change (if h+3≤h+1 ∧ h+1<h+2+(r : Int) then false else
      put (put mid.tape (h-1) true) (h+2) false (h+1))=false
    rw [if_neg (by omega),put_other _ _ _ _ (by omega),put_other _ _ _ _ (by omega)]
    rw [hframe (h+1) (by omega) (Or.inl (by omega))]
    exact hzero
  have hz : ∀ i : Nat, i<r-1 → out (a+((2*z : Nat):Int)+6+(i : Int))=false := by
    intro i hi
    have hp : a+((2*z : Nat):Int)+6+(i : Int)=h+2+(i : Int) := by omega
    rw [hp]
    dsimp [out,u]
    rw [put_other _ _ _ _ (by omega)]
    by_cases hi0 : i=0
    · subst i
      simp [clearRange,put]
    · change (if h+3≤h+2+(i : Int) ∧ h+2+(i : Int)<h+2+(r : Int) then false else
        put (put mid.tape (h-1) true) (h+2) false (h+2+(i : Int)))=false
      rw [if_pos (by omega)]
  have hm : out (a+((2*z : Nat):Int)+6+((r-1 : Nat):Int))=true := by
    have hp : a+((2*z : Nat):Int)+6+((r-1 : Nat):Int)=h+1+(r : Int) := by omega
    rw [hp]
    simp [out,put]
  have hstart : a+((2*z : Nat):Int)+2=h-2 := by omega
  have hcycle := terminal_unit_cycle out a z (r-1) (by omega) hl hwindow hleft hmarker h0 h1 hz hm
  rw [hstart] at hcycle
  dsimp only at hcycle
  have hd : a+((2*z : Nat):Int)+4=h := by omega
  rw [hd] at hcycle
  have hend : h+((r-1 : Nat):Int)=h+(r : Int)-1 := by omega
  have hupper : h+2+((r-1 : Nat):Int)=h+1+(r : Int) := by omega
  rw [hend,hupper] at hcycle
  let final := fillRange (setAt h out) (h+2) (h+1+(r : Int))
  have hfinal : ∀ q, base≤q → final q=mid.tape q := by
    intro q hq
    change (if h+2≤q ∧ q<h+1+(r : Int) then true else setAt h out q)=mid.tape q
    rw [if_neg (by dsimp [base] at hq; omega)]
    change (if q=h then true else out q)=mid.tape q
    rw [if_neg (by dsimp [base] at hq; omega)]
    exact hright q hq
  have hb : Holds final base (encode values) := by
    apply holds_transport mid.tape final base _ hbank
    intro q hq _
    symm
    exact hfinal q hq
  have hc := segAdd machine _ _ _ ((encode values).length+r+2+(2*r+7)) (4*z+(r-1)+12) h83 hcycle
  refine ⟨mid,hstate,hfirst,hb,hfinal,?_⟩
  exact hc

#print axioms dispatch_through_terminal_exact
end Shared.Beeping.NPcoNP.NativeUnitTerminalBridgeExact
