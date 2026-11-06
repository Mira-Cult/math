import Shared.Beeping.NPcoNP.NativeUnitCarryExact83

/-! Unit-selector increment and complete finite return to state 83,
parameterized by the supplied control word and unary bank. -/
namespace Shared.Beeping.NPcoNP.NativeUnit261CycleExact83
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeUnit261Return1
open Shared.Beeping.NPcoNP.NativeUnitCarryExact83
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- The full local macro reaches state 83 with the updated bank intact in an exact number of steps.
This is a supplied-layout theorem; the cycle invariant is not assumed proved. -/
theorem dispatch_increment_to83_exact (r v : Nat) (rest : List Nat) (h : Int) (t : Int → Bool)
    (hr : 0<r) (hpre : t (h-1)=false) (hone : t h=true) (hzero : t (h+1)=false)
    (scanword : Holds t (h+2) (List.replicate r true ++ [false]))
    (bank : Holds t (h+2+(r : Int)+1) (encode (v::rest) ++ [false])) :
    let base := h+2+(r : Int)+1
    let values := (v+1)::rest
    ∃ mid : Config 284, mid.state=23 ∧
      Holds mid.tape base (encode values) ∧
      silentSegment machine (cfg 261 h t) mid (r+v+6+(encode rest).length) ∧
      let u := put (put mid.tape (h-1) true) (h+2) false
      let out := put (clearRange u (h+3) (h+2+(r : Int))) (h+1+(r : Int)) true
      Holds out base (encode values) ∧
      (∀ q, base≤q → out q=mid.tape q) ∧
      silentSegment machine mid (cfg 83 (h-2) out) ((encode values).length+r+2+(2*r+7)) := by
  dsimp only
  let base := h+2+(r : Int)+1
  let values := (v+1)::rest
  obtain ⟨mid,hstate,hbank,hmark,hframe,hfirst,hreturn⟩ :=
    dispatch_increment_return1 r v rest h t hr hone hzero scanword bank
  have hpre' : mid.tape (h-1)=false := by
    rw [hframe (h-1) (by omega) (Or.inl (by omega))]
    exact hpre
  have hzero' : mid.tape (h+1)=false := by
    rw [hframe (h+1) (by omega) (Or.inl (by omega))]
    exact hzero
  have hscan : Holds mid.tape (h+2) (List.replicate r true ++ [false]) := by
    apply holds_transport t mid.tape _ _ scanword
    intro q hq hq'
    symm
    apply hframe q (by omega)
    left
    have hl : (List.replicate r true ++ [false]).length=r+1 := by simp
    rw [hl] at hq'
    omega
  have hcarry := carry_to83_exact r h mid.tape hr hpre' hmark hzero' hscan
  let u := put (put mid.tape (h-1) true) (h+2) false
  let out := put (clearRange u (h+3) (h+2+(r : Int))) (h+1+(r : Int)) true
  have hright : ∀ q, base≤q → out q=mid.tape q := by
    intro q hq
    change put (clearRange u (h+3) (h+2+(r : Int))) (h+1+(r : Int)) true q=mid.tape q
    rw [put_other _ _ _ _ (by dsimp [base] at hq; omega)]
    change (if h+3≤q ∧ q<h+2+(r : Int) then false else u q)=mid.tape q
    rw [if_neg (by dsimp [base] at hq; omega)]
    change put (put mid.tape (h-1) true) (h+2) false q=mid.tape q
    rw [put_other _ _ _ _ (by dsimp [base] at hq; omega),
      put_other _ _ _ _ (by dsimp [base] at hq; omega)]
  have hbank' : Holds out base (encode values) := by
    apply holds_transport mid.tape out base _ hbank
    intro q hq _
    symm
    exact hright q hq
  refine ⟨mid,hstate,hbank,hfirst,hbank',hright,?_⟩
  exact segAdd machine _ _ _ ((encode values).length+r+2) (2*r+7) hreturn hcarry

#print axioms dispatch_increment_to83_exact
end Shared.Beeping.NPcoNP.NativeUnit261CycleExact83
