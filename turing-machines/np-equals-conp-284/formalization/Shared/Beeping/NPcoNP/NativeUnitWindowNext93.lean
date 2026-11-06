import Shared.Beeping.NPcoNP.NativeUnitWindowIncrement83

/-! Compose the exact unit increment with the next selector whenever its
fourteen-block window lies immediately to the left of the new marker. -/
namespace Shared.Beeping.NPcoNP.NativeUnitWindowNext93
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeUnitWindowIncrement83
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- A separately supplied next control window survives the increment and
is read completely. The prefix and marker facts are conclusions of the
physical segment; the next window is an explicit layout premise. -/
theorem unit_increment_next93 (t : Int → Bool) (a b : Int) (k z r v : Nat)
    (zs rest next : List Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ 1::0::z::zs)))
    (hr : 0<r)
    (pre : t (a+((2*k : Nat):Int)+3)=false)
    (scanword : Holds t (a+((2*k : Nat):Int)+6) (List.replicate r true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+6+(r : Int)+1) (encode (v::rest) ++ [false]))
    (hn : next.length=14)
    (hpos : b+((encode next).length : Int)=a+((2*k : Nat):Int)+3)
    (nextWindow : Holds t b (markerWindow next)) (before : t (b-1)=true) :
    let d := a+((2*k : Nat):Int)+4
    let base := d+2+(r : Int)+1
    let values := (v+1)::rest
    ∃ mid : Config 284, mid.state=23 ∧
      silentSegment machine (cfg 93 a t) mid (2*k+4+(r+v+6+(encode rest).length)) ∧
      let u := put (put mid.tape (d-1) true) (d+2) false
      let out := put (clearRange u (d+3) (d+2+(r : Int))) (d+1+(r : Int)) true
      Holds out base (encode values) ∧ Holds out b (markerWindow next) ∧
      out (b-1)=true ∧ out (d-1)=true ∧ (∀ q, q<d-1 → out q=t q) ∧
      silentSegment machine mid (cfg 93 b out)
        ((encode values).length+r+2+(2*r+7)+((encode next).length+1)) := by
  dsimp only
  let d := a+((2*k : Nat):Int)+4
  let base := d+2+(r : Int)+1
  let values := (v+1)::rest
  obtain ⟨mid,hs,_hmid,hfirst,hbank,_hframe,hmark,hprefix,hret⟩ :=
    unit_window_increment_to83_exact t a k z r v zs rest window hr pre scanword bank
  let u := put (put mid.tape (d-1) true) (d+2) false
  let out := put (clearRange u (d+3) (d+2+(r : Int))) (d+1+(r : Int)) true
  have hpos' : b+((encode next).length : Int)=d-1 := by dsimp [d]; omega
  have hwindow : Holds out b (markerWindow next) := by
    apply holds_transport t out b _ nextWindow
    intro q _ hq
    symm
    apply hprefix
    rw [markerWindow_length] at hq
    omega
  have hbefore : out (b-1)=true := by
    have he : out (b-1)=t (b-1) := hprefix (b-1) (by omega)
    exact he.trans before
  have hnext := marker_window_to93 out b next hn hwindow hbefore
  have hnext' : silentSegment machine (cfg 83 (d-2) out) (cfg 93 b out)
      ((encode next).length+1) := by
    have he : b+((encode next).length : Int)-1=d-2 := by omega
    simpa only [he] using hnext
  refine ⟨mid,hs,hfirst,hbank,hwindow,hbefore,hmark,hprefix,?_⟩
  exact segAdd machine _ _ _ ((encode values).length+r+2+(2*r+7))
    ((encode next).length+1) hret hnext'

#print axioms unit_increment_next93
end Shared.Beeping.NPcoNP.NativeUnitWindowNext93
