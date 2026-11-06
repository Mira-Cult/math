import Shared.Beeping.NPcoNP.NativeHalfScanStep

/-! Exact one-transition equations for the native-HALF cycle's backward
suffix-shift states. These do not by themselves establish a complete shift,
termination, or a register-machine simulation. -/
namespace Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284

theorem shift34_zero (h : Int) (tape : Int → Bool) (ht : tape h = false) :
    machine.step ⟨34, h, tape⟩ =
      (⟨35, h-1, (⟨34, h, tape⟩ : Config 284).write true⟩, false) := by
  simp [Machine.step, ht, row34_zero, Move.apply]

theorem shift34_one (h : Int) (tape : Int → Bool) (ht : tape h = true) :
    machine.step ⟨34, h, tape⟩ = (⟨34, h-1, tape⟩, false) := by
  have hw : (⟨34, h, tape⟩ : Config 284).write true = tape := by
    rw [← ht]
    exact write_current _
  simp [Machine.step, ht, row34_one, Move.apply, hw]

theorem shift35_zero (h : Int) (tape : Int → Bool) (ht : tape h = false) :
    machine.step ⟨35, h, tape⟩ = (⟨31, h-1, tape⟩, false) := by
  have hw : (⟨35, h, tape⟩ : Config 284).write false = tape := by
    rw [← ht]
    exact write_current _
  simp [Machine.step, ht, row35_zero, Move.apply, hw]

theorem shift35_one (h : Int) (tape : Int → Bool) (ht : tape h = true) :
    machine.step ⟨35, h, tape⟩ =
      (⟨34, h-1, (⟨35, h, tape⟩ : Config 284).write false⟩, false) := by
  simp [Machine.step, ht, row35_one, Move.apply]

end Shared.Beeping.NPcoNP.NativeHalfRows
