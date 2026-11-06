import Shared.Beeping.NPcoNP.NativeAllBankScan
import Shared.Beeping.NPcoNP.Native51Prepare

/-! Uniform zero-entry preparation for all ordinary operation states. The
selector return and graph-level effect are separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeAllBankZeroPrepare
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.Native51Prepare
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem ordinary_zero_row (n : Fin 12) (inc : Bool) :
    machine.table.row (operationAt n inc) false=machine.table.row 51 false := by
  have all : ∀ (n : Fin 12) (inc : Bool),
      machine.table.row (operationAt n inc) false=machine.table.row 51 false := by decide
  exact all n inc

theorem ordinary_zero_step (n : Fin 12) (inc : Bool) (x : Int) (t : Int → Bool)
    (zero : t x=false) :
    machine.step (cfg (operationAt n inc) x t)=machine.step (cfg 51 x t) := by
  simp [Machine.step,cfg,zero,ordinary_zero_row]
  rfl

/-- Segments of positive duration coincide when their initial literal
transitions coincide and emit no event. -/
theorem replace_first_step (c d e : Config 284) (k : Nat)
    (same : machine.step c=machine.step d) (silent : (machine.step c).2=false)
    (segment : silentSegment machine c e (k+1)) : silentSegment machine d e (k+1) := by
  let z := (machine.step c).1
  have a : silentSegment machine c z 1 := oneSeg machine _ _ (by
    have he : machine.step c=((machine.step c).1,(machine.step c).2) := by cases machine.step c; rfl
    simpa [z,silent] using he)
  have b : silentSegment machine d z 1 := oneSeg machine _ _ (by
    rw [←same]
    have he : machine.step c=((machine.step c).1,(machine.step c).2) := by cases machine.step c; rfl
    simpa [z,silent] using he)
  have rest : silentSegment machine z e k := by
    constructor
    · have hh := segment.1
      rw [show k+1=1+k by omega,WordEventSystem.advance_add,a.1] at hh
      exact hh
    · have hh := segment.2
      rw [show k+1=1+k by omega,WordEventSystem.wordFrom_add,a.1,a.2] at hh
      simpa using hh
  simpa [Nat.add_comm] using segAdd machine _ _ _ 1 k b rest

/-- Every ordinary entry state has the same exact zero preparation as state 51,
including the empty zero run. -/
theorem ordinary_zero_prepare (n : Fin 12) (inc : Bool) (x : Int) (t : Int → Bool) (k : Nat)
    (h0 : t x=false) (h1 : t (x+1)=false) (h2 : t (x+2)=false)
    (zeros : ∀ i : Nat, i<k → t (x+3+(i : Int))=false)
    (marker : t (x+3+(k : Int))=true) :
    let out := fillRange (setAt x t) (x+3) (x+3+(k : Int))
    let head := if k=0 then x-1 else x+3+(k : Int)-2
    let duration := if k=0 then 7 else k+5
    silentSegment machine (cfg (operationAt n inc) x t) (cfg 83 head out) duration := by
  dsimp only
  have h51 := zero_prepare_to83_exact x t k h0 h1 h2 zeros marker
  have heq := (ordinary_zero_step n inc x t h0).symm
  have hevent : (machine.step (cfg 51 x t)).2=false := by
    rw [step51_zero x t h0]
  cases k with
  | zero =>
    exact replace_first_step _ _ _ 6 heq hevent h51
  | succ k =>
    simp only [Nat.succ_ne_zero,if_false] at h51 ⊢
    have hd : k+1+5=(k+5)+1 := by omega
    rw [hd] at h51 ⊢
    exact replace_first_step _ _ _ (k+5) heq hevent h51

#print axioms ordinary_zero_prepare
end Shared.Beeping.NPcoNP.NativeAllBankZeroPrepare
