import Shared.Beeping.NPcoNP.NativeUnitTerminalLayout
import Shared.Beeping.NPcoNP.NativeUnitBankPadding
import Shared.Beeping.NPcoNP.NativeManyTerminalWindow

/-! Compose the unit/terminal layout transition with the following positive
terminal-many dispatch, charging both segments and all tape writes. -/
namespace Shared.Beeping.NPcoNP.NativeUnitTerminalMany
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeUnitControlMerge
open Shared.Beeping.NPcoNP.NativeUnitTerminalLayout
open Shared.Beeping.NPcoNP.NativeUnitBankPadding
open Shared.Beeping.NPcoNP.NativeManyTerminalWindow
open Shared.Beeping.NPcoNP.Bootstrap284BankShape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

/-- A prepared unit/terminal cycle with three bank blanks executes the next
positive terminal-many selector through its state-23 bank update. Both event
segments are silent and the intermediate duration is strictly positive. -/
theorem unit_terminal_to_many (t : Int → Bool) (a b : Int) (k z r v : Nat)
    (rest : List Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ [1,0,z])))
    (hlen : (List.replicate k 0 ++ [1,0,z]).length=14)
    (hr : 1<r)
    (pre : t (a+((2*k : Nat):Int)+3)=false)
    (scanword : Holds t (a+((2*k : Nat):Int)+6) (List.replicate r true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+6+(r : Int)+1) (encode (v::rest) ++ [false,false,false]))
    (terminalPos : b+((2*13 : Nat):Int)+3=a+((2*k : Nat):Int)+3)
    (terminal : Holds t b (markerWindow (List.replicate 13 0 ++ [1])))
    (terminalBefore : t (b-1)=true)
    (left0 : t (a-2)=false) (left1 : t (a-1)=true) (before : t (a-3)=true)
    (marker : t (a+((encode (List.replicate k 0 ++ [1,0,z])).length : Int))=true)
    (alignment : a+((encode (List.replicate k 0 ++ [1,0,z])).length : Int)=
      a+((2*k : Nat):Int)+4+(r : Int)) :
    let d := a+((2*k : Nat):Int)+4
    let base := d+2+(r : Int)+1
    let values := (v+1)::rest
    let next := List.replicate (k+1) 0 ++ [3,z]
    ∃ (mid : Config 284) (n : Nat), mid.state=23 ∧ 0<n ∧
      let final := setAt (d-1) (setAt d mid.tape)
      let suffix := List.replicate v true ++ rest.flatMap (fun z => false :: List.replicate (z+1) true)
      let out := Shared.Beeping.NPcoNP.NativeHalfSweep.spec (Shared.Beeping.NPcoNP.NativeHalfState16Progress.clearAt d final)
        (base+2+((suffix.length : Nat):Int)) (suffix.length+2)
      Holds final (a-2) (markerWindow next) ∧
      Holds final base (encode values ++ [false,false]) ∧
      Holds out base (encode (v::rest) ++ [true,false,false]) ∧
      silentSegment machine (cfg 93 a t) (cfg 23 (base-2) out)
        (((2*k+4)+(r+v+6+(encode rest).length)+
          ((encode values).length+r+2+n+(4*13+(r-1)+12))) +
          ((encode next).length+1+(2*(k+1)+z+2+2*suffix.length+16))) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let base := d+2+(r : Int)+1
  let values := (v+1)::rest
  let next := List.replicate (k+1) 0 ++ [3,z]
  have hbank2 : Holds t (a+((2*k : Nat):Int)+6+(r : Int)+1) (encode (v::rest) ++ [false,false]) := by
    apply holds_prefix_word t _ (encode (v::rest) ++ [false,false]) [false]
    simpa [List.append_assoc] using bank
  have hw : Holds t a (markerWindow (List.replicate k 0 ++ 1::0::z::[])) := by simpa using window
  obtain ⟨mid,n,hs,hn,hnextlen,hwindow,hbefore,_hmark,hbank1,hext,hframe,hhead,hseg⟩ :=
    unit_terminal_next_layout t a b k z r v [] rest hw (by simpa using hlen) hr pre scanword hbank2
      terminalPos terminal terminalBefore left0 left1 before (by simpa using marker) (by simpa using alignment)
  let final := setAt (d-1) (setAt d mid.tape)
  have hinput : Holds t base (encode (v::rest) ++ List.replicate (2+1) false) := by
    have he : base=a+((2*k : Nat):Int)+6+(r : Int)+1 := by dsimp [base,d]; omega
    rw [he]
    simpa using bank
  have hupdated : Holds final base (encode values) := by
    apply holds_prefix_word final base (encode values) [false]
    exact hbank1
  have hright : ∀ q, base+(((v+1)+(encode rest).length : Nat):Int)<q → final q=t q := by
    intro q hq
    apply hframe q
    · dsimp [base] at hq
      omega
    · exact Or.inr hq
  have hpadded : Holds final base (encode values ++ [false,false]) := by
    have hh := increment_preserves_padding t final base v 2 rest hinput hupdated hright
    simpa [values] using hh
  have hrz : r=z+3 := by
    have he : (encode (List.replicate k 0 ++ [1,0,z])).length=2*k+z+7 := by
      simp [encode_append,zeros_length,encode,block_length]
      omega
    rw [he] at alignment
    push_cast at alignment
    omega
  let suffix := List.replicate v true ++ rest.flatMap (fun z => false :: List.replicate (z+1) true)
  let out := Shared.Beeping.NPcoNP.NativeHalfSweep.spec (Shared.Beeping.NPcoNP.NativeHalfState16Progress.clearAt d final)
    (base+2+((suffix.length : Nat):Int)) (suffix.length+2)
  have hnextlen' : (List.replicate (k+1) 0 ++ [0+3,z]).length=14 := by simpa [next] using hnextlen
  have hwindow' : Holds final (a-2) (markerWindow (List.replicate (k+1) 0 ++ [0+3,z])) := hwindow
  have hbefore' : final (a-2-1)=true := by
    have he : a-2-1=a-3 := by omega
    simpa only [he] using hbefore
  have hext' : Holds final ((a-2)+((encode (List.replicate (k+1) 0 ++ [0+3,z])).length : Int))
      (List.replicate 2 true ++ [false]) := by
    have he : (a-2)+((encode (List.replicate (k+1) 0 ++ [0+3,z])).length : Int)=
        a+((encode (List.replicate k 0 ++ [1,0,z])).length : Int) := by
      have hh := merged_window_length k z []
      rw [hh]
      push_cast
      omega
    rw [he]
    exact hext
  have hbank' : Holds final ((a-2)+((2*(k+1) : Nat):Int)+4+(0:Int)+(z:Int)+(2:Int)+4)
      (encode ((v+1)::rest) ++ [false,false]) := by
    have he : (a-2)+((2*(k+1) : Nat):Int)+4+(0:Int)+(z:Int)+(2:Int)+4=base := by
      dsimp [base,d]
      omega
    rw [he]
    exact hpadded
  obtain ⟨hout,houtframe,hdispatch⟩ := terminal_selector_to_bank final (a-2) (k+1) 0 z 2 v rest
    hnextlen' hbefore' hwindow' hext' hbank'
  have hehead : (a-2)+((encode (List.replicate (k+1) 0 ++ [0+3,z])).length : Int)-1=
      d+(r : Int)-1 := hhead
  have hex : (a-2)+((2*(k+1) : Nat):Int)+4+(0:Int)+(z:Int)+(2:Int)+4=base := by
    dsimp [base,d]
    omega
  have hed : (a-2)+((2*(k+1) : Nat):Int)+4=d := by dsimp [d]; omega
  norm_num only [Nat.cast_ofNat,Nat.cast_zero] at hout houtframe hdispatch
  rw [hex] at hout houtframe hdispatch
  rw [hed] at hout houtframe hdispatch
  have hdispatch' : silentSegment machine (cfg 83 (d+(r : Int)-1) final) (cfg 23 (base-2) out)
      ((encode next).length+1+(2*(k+1)+z+2+2*suffix.length+16)) := by
    simpa only [hehead,hed,next,suffix,out,Nat.zero_add,Nat.add_zero] using hdispatch
  have hall := segAdd machine _ _ _
    ((2*k+4)+(r+v+6+(encode rest).length)+((encode values).length+r+2+n+(4*13+(r-1)+12)))
    ((encode next).length+1+(2*(k+1)+z+2+2*suffix.length+16)) hseg hdispatch'
  exact ⟨mid,n,hs,hn,hwindow,hpadded,hout,hall⟩

#print axioms unit_terminal_to_many
end Shared.Beeping.NPcoNP.NativeUnitTerminalMany
