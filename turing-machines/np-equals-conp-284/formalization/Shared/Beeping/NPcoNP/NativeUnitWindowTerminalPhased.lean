import Shared.Beeping.NPcoNP.NativeUnitTerminalSummaryExact
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue

/-! Exact physical unit/terminal macro with an explicit state-23 phase
and separate silent segments on each side. -/
namespace Shared.Beeping.NPcoNP.NativeUnitWindowTerminalPhased
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
theorem unit_through_terminal_phased_exact (t : Int → Bool) (a b : Int) (k z r v : Nat)
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
      silentSegment machine (cfg 93 a t) mid
        ((2*k+4)+(r+v+6+(encode rest).length)) ∧
      let final := setAt (d-1) (setAt d mid.tape)
      Holds final base (encode values) ∧
      (∀ q, q≠d-1 → (q<base ∨ last<q) → final q=t q) ∧
      silentSegment machine mid (cfg 83 (d+(r : Int)-1) final)
        ((encode values).length+r+2+(2*r+7)+(4*13+(r-1)+12)) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let base := d+2+(r : Int)+1
  let values := (v+1)::rest
  have h261 := marker_window_to_one t a k (0::z::zs) (by simp) window
  obtain ⟨hone,hzeroWord⟩ := one_marker_tail t a k 0 z zs window
  have hzero : t (d+1)=false := by simpa [d] using hzeroWord.1
  have hpre : t (d-1)=false := by
    have he : d-1=a+((2*k : Nat):Int)+3 := by dsimp [d]; omega
    rw [he]
    exact pre
  have hscan : Holds t (d+2) (List.replicate r true ++ [false]) := by
    have he : d+2=a+((2*k : Nat):Int)+6 := by dsimp [d]; omega
    rw [he]
    exact scanword
  have hbank : Holds t base (encode (v::rest) ++ [false]) := by
    have he : base=a+((2*k : Nat):Int)+6+(r : Int)+1 := by dsimp [base,d]; omega
    rw [he]
    exact bank
  have hp : b+((2*13 : Nat):Int)+3=d-1 := by dsimp [d]; omega
  obtain ⟨mid,hs,hinc,hout,hframe,hreturn⟩ :=
    dispatch_terminal_net_exact r v 13 rest d b t hr hpre hone hzero hscan hbank hl hp terminal before
  have hpreseg := segAdd machine _ _ _ (2*k+4) (r+v+6+(encode rest).length) h261 hinc
  exact ⟨mid,hs,hpreseg,hout,hframe,hreturn⟩

#print axioms unit_through_terminal_phased_exact
end Shared.Beeping.NPcoNP.NativeUnitWindowTerminalPhased
