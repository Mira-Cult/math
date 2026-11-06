import Shared.Beeping.NPcoNP.NativeUnit261CycleExact83
import Shared.Beeping.NPcoNP.NativeUnitCarry83

/-! Unit-selector increment and complete finite return to state 83,
parameterized by the supplied control word and unary bank. -/
namespace Shared.Beeping.NPcoNP.NativeUnit261Cycle83
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeUnit261Return1
open Shared.Beeping.NPcoNP.NativeUnitCarry83
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- The full local macro reaches state 83 with the updated bank intact.
This is a supplied-layout theorem; the cycle invariant is not assumed proved. -/
theorem dispatch_increment_to83 (r v : Nat) (rest : List Nat) (h : Int) (t : Int → Bool)
    (hr : 0<r) (hpre : t (h-1)=false) (hone : t h=true) (hzero : t (h+1)=false)
    (scanword : Holds t (h+2) (List.replicate r true ++ [false]))
    (bank : Holds t (h+2+(r : Int)+1) (encode (v::rest) ++ [false])) :
    let base := h+2+(r : Int)+1
    let values := (v+1)::rest
    ∃ (mid : Config 284) (n : Nat), mid.state=23 ∧
      Holds mid.tape base (encode values) ∧
      silentSegment machine (cfg 261 h t) mid (r+v+6+(encode rest).length) ∧ 0<n ∧
      let u := put (put mid.tape (h-1) true) (h+2) false
      let out := put (clearRange u (h+3) (h+2+(r : Int))) (h+1+(r : Int)) true
      Holds out base (encode values) ∧
      (∀ q, base≤q → out q=mid.tape q) ∧
      silentSegment machine mid (cfg 83 (h-2) out) ((encode values).length+r+2+n) := by
  dsimp only
  obtain ⟨mid,hstate,hbank,hfirst,hout,hright,hseg⟩ :=
    Shared.Beeping.NPcoNP.NativeUnit261CycleExact83.dispatch_increment_to83_exact
      r v rest h t hr hpre hone hzero scanword bank
  exact ⟨mid,2*r+7,hstate,hbank,hfirst,by omega,hout,hright,hseg⟩

#print axioms dispatch_increment_to83
end Shared.Beeping.NPcoNP.NativeUnit261Cycle83
