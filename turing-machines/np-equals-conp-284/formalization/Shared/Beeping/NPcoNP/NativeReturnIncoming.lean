import Shared.Beeping.NPcoNP.NativeHalfState28Exit
import Shared.Beeping.NPcoNP.NativeHalfState1Scan
import Shared.Beeping.NPcoNP.NativeHalfState27Scan

/-! A blank-start invariant for the literal return scanner. -/
namespace Shared.Beeping.NPcoNP.NativeReturnMarkerInvariant
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState27Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Progress
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000

theorem incoming27 (q : Fin 284) (b : Bool)
    (h : (machine.table.row q b).next=27) :
    (q=1 ∧ b=false) ∨ (q=27 ∧ b=false) := by
  have hall : ∀ (q : Fin 284) (b : Bool), (machine.table.row q b).next=27 →
      (q=1 ∧ b=false) ∨ (q=27 ∧ b=false) := by decide
  exact hall q b h

theorem incoming28 (q : Fin 284) (b : Bool)
    (h : (machine.table.row q b).next=28) :
    (q=27 ∧ b=true) ∨ (q=28 ∧ b=true) := by
  have hall : ∀ (q : Fin 284) (b : Bool), (machine.table.row q b).next=28 →
      (q=27 ∧ b=true) ∨ (q=28 ∧ b=true) := by decide
  exact hall q b h


#print axioms incoming27
#print axioms incoming28
end Shared.Beeping.NPcoNP.NativeReturnMarkerInvariant
