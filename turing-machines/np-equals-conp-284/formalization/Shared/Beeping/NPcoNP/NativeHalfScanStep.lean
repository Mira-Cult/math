import Shared.Beeping.NPcoNP.NativeHalfRows

/-! Exact one-transition equations for the two forward scan states of the
literal 284-state machine. A whole-suffix termination theorem requires a
separate proof and is not asserted here. -/
namespace Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284

theorem write_current {n : Nat} (c : Config n) : c.write (c.tape c.head) = c.tape := by
  funext i
  by_cases h : i = c.head
  · subst i
    simp [Config.write]
  · simp [Config.write, h]

theorem scan32_zero (h : Int) (tape : Int → Bool) (ht : tape h = false) :
    machine.step ⟨32, h, tape⟩ = (⟨33, h+1, tape⟩, false) := by
  have hw : (⟨32, h, tape⟩ : Config 284).write false = tape := by
    rw [← ht]
    exact write_current _
  simp [Machine.step, ht, row32_zero, Move.apply, hw]

theorem scan32_one (h : Int) (tape : Int → Bool) (ht : tape h = true) :
    machine.step ⟨32, h, tape⟩ = (⟨32, h+1, tape⟩, false) := by
  have hw : (⟨32, h, tape⟩ : Config 284).write true = tape := by
    rw [← ht]
    exact write_current _
  simp [Machine.step, ht, row32_one, Move.apply, hw]

theorem scan33_zero (h : Int) (tape : Int → Bool) (ht : tape h = false) :
    machine.step ⟨33, h, tape⟩ = (⟨34, h-1, tape⟩, false) := by
  have hw : (⟨33, h, tape⟩ : Config 284).write false = tape := by
    rw [← ht]
    exact write_current _
  simp [Machine.step, ht, row33_zero, Move.apply, hw]

theorem scan33_one (h : Int) (tape : Int → Bool) (ht : tape h = true) :
    machine.step ⟨33, h, tape⟩ = (⟨32, h+1, tape⟩, false) := by
  have hw : (⟨33, h, tape⟩ : Config 284).write true = tape := by
    rw [← ht]
    exact write_current _
  simp [Machine.step, ht, row33_one, Move.apply, hw]

end Shared.Beeping.NPcoNP.NativeHalfRows
