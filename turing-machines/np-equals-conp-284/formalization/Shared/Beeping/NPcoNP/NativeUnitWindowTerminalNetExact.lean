import Shared.Beeping.NPcoNP.NativeUnitWindowTerminalPhased
import Shared.Beeping.NPcoNP.NativeUnitTerminalSummaryExact
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue

/-! Compose a unit selector and increment with a supplied terminal selector,
including the latter's fill return and net tape update. -/
namespace Shared.Beeping.NPcoNP.NativeUnitWindowTerminalNetExact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerDispatch
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeUnitTerminalSummaryExact
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- From a prepared unit window, increment the first bank value and run the
supplied terminal-selector return. The output frame records the complete net
control change outside the incremented bank. -/
theorem unit_through_terminal_net_exact (t : Int → Bool) (a b : Int) (k z r v : Nat)
    (zs rest : List Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ 1::0::z::zs)))
    (hr : 1<r)
    (pre : t (a+((2*k : Nat):Int)+3)=false)
    (scanword : Holds t (a+((2*k : Nat):Int)+6) (List.replicate r true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+6+(r : Int)+1) (encode (v::rest) ++ [false]))
    (hl : (List.replicate 13 0 ++ [1]).length=14)
    (hpos : b+((2*13 : Nat):Int)+3=a+((2*k : Nat):Int)+3)
    (terminal : Holds t b (markerWindow (List.replicate 13 0 ++ [1])))
    (before : t (b-1)=true) :
    let d := a+((2*k : Nat):Int)+4
    let base := d+2+(r : Int)+1
    let last := base+(((v+1)+(encode rest).length : Nat):Int)
    let values := (v+1)::rest
    ∃ mid : Config 284, mid.state=23 ∧
      let final := setAt (d-1) (setAt d mid.tape)
      Holds final base (encode values) ∧
      (∀ q, q≠d-1 → (q<base ∨ last<q) → final q=t q) ∧
      silentSegment machine (cfg 93 a t) (cfg 83 (d+(r : Int)-1) final)
        ((2*k+4)+(r+v+6+(encode rest).length)+
          ((encode values).length+r+2+(2*r+7)+(4*13+(r-1)+12))) := by
  dsimp only
  obtain ⟨mid,hs,hfirst,hout,hframe,hreturn⟩ :=
    Shared.Beeping.NPcoNP.NativeUnitWindowTerminalPhased.unit_through_terminal_phased_exact
      t a b k z r v zs rest window hr pre scanword bank hl hpos terminal before
  exact ⟨mid,hs,hout,hframe,
    segAdd machine _ _ _
      ((2*k+4)+(r+v+6+(encode rest).length))
      ((encode ((v+1)::rest)).length+r+2+(2*r+7)+(4*13+(r-1)+12))
      hfirst hreturn⟩

#print axioms unit_through_terminal_net_exact
end Shared.Beeping.NPcoNP.NativeUnitWindowTerminalNetExact
