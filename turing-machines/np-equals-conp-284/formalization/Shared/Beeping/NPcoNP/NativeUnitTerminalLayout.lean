import Shared.Beeping.NPcoNP.NativeUnitControlMerge
import Shared.Beeping.NPcoNP.NativeUnitTerminalLayoutExact
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
import Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

/-! The compound unit/terminal macro restores a marked selector layout,
with an updated bank and an explicitly protected trailing sentinel. -/
namespace Shared.Beeping.NPcoNP.NativeUnitTerminalLayout
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeUnitWindowTerminalNet
open Shared.Beeping.NPcoNP.NativeUnitControlMerge
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- One compound unit/terminal step produces the next fourteen-block
selector, its two markers, and an incremented bank with one trailing zero.
Two initial bank sentinels are required to retain the latter property. -/
theorem unit_terminal_next_layout (t : Int → Bool) (a b : Int) (k z r v : Nat)
    (zs rest : List Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ 1::0::z::zs)))
    (hlen : (List.replicate k 0 ++ 1::0::z::zs).length=14)
    (hr : 1<r)
    (pre : t (a+((2*k : Nat):Int)+3)=false)
    (scanword : Holds t (a+((2*k : Nat):Int)+6) (List.replicate r true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+6+(r : Int)+1) (encode (v::rest) ++ [false,false]))
    (terminalPos : b+((2*13 : Nat):Int)+3=a+((2*k : Nat):Int)+3)
    (terminal : Holds t b (markerWindow (List.replicate 13 0 ++ [1])))
    (terminalBefore : t (b-1)=true)
    (left0 : t (a-2)=false) (left1 : t (a-1)=true) (before : t (a-3)=true)
    (marker : t (a+((encode (List.replicate k 0 ++ 1::0::z::zs)).length : Int))=true)
    (alignment : a+((encode (List.replicate k 0 ++ 1::0::z::zs)).length : Int)=
      a+((2*k : Nat):Int)+4+(r : Int)) :
    let d := a+((2*k : Nat):Int)+4
    let base := d+2+(r : Int)+1
    let values := (v+1)::rest
    let next := List.replicate (k+1) 0 ++ 3::z::zs
    ∃ (mid : Config 284) (n : Nat), mid.state=23 ∧ 0<n ∧ next.length=14 ∧
      let final := setAt (d-1) (setAt d mid.tape)
      Holds final (a-2) (markerWindow next) ∧ final (a-3)=true ∧
      final (a+((encode (List.replicate k 0 ++ 1::0::z::zs)).length : Int))=true ∧
      Holds final base (encode values ++ [false]) ∧
      Holds final (a+((encode (List.replicate k 0 ++ 1::0::z::zs)).length : Int))
        (List.replicate 2 true ++ [false]) ∧
      (∀ q, q≠d-1 → (q<base ∨ base+(((v+1)+(encode rest).length : Nat):Int)<q) → final q=t q) ∧
      (a-2)+((encode next).length : Int)-1=d+(r : Int)-1 ∧
      silentSegment machine (cfg 93 a t) (cfg 83 (d+(r : Int)-1) final)
        ((2*k+4)+(r+v+6+(encode rest).length)+
          ((encode values).length+r+2+n+(4*13+(r-1)+12))) := by
  dsimp only
  obtain ⟨mid,hs,hfirst,hnext,hwindow,hbefore,hmarker,hbank,hext,hframe,hhead,hreturn⟩ :=
    Shared.Beeping.NPcoNP.NativeUnitTerminalLayoutExact.unit_terminal_next_layout_exact
      t a b k z r v zs rest window hlen hr pre scanword bank terminalPos terminal
      terminalBefore left0 left1 before marker alignment
  have hseg := segAdd machine _ _ _
    ((2*k+4)+(r+v+6+(encode rest).length))
    ((encode ((v+1)::rest)).length+r+2+(2*r+7)+(4*13+(r-1)+12)) hfirst hreturn
  exact ⟨mid,2*r+7,hs,by omega,hnext,hwindow,hbefore,hmarker,hbank,hext,hframe,hhead,hseg⟩

#print axioms unit_terminal_next_layout
end Shared.Beeping.NPcoNP.NativeUnitTerminalLayout
