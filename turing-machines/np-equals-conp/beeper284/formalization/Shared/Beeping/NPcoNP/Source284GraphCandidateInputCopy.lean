import Shared.Beeping.NPcoNP.Parent290Coalesced

/-! The checked graph's candidate input-copy block. This module starts
from a supplied register bank; it does not prove physical reachability or the
correctness of the subsequent bounded evaluator. -/
namespace Shared.Beeping.NPcoNP.Source284GraphCandidateInputCopy

open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced

abbrev Bank := PASoundness.RegisterMachine.Bank 12

/-- The four mutable registers in this graph block. -/
def bank (b : Bank) (x y z w : Nat) : Bank :=
  fun i => if i = 4 then x else if i = 1 then y else if i = 9 then z else if i = 10 then w else b i

@[simp] theorem bank4 (b : Bank) (x y z w : Nat) : bank b x y z w 4 = x := by simp [bank]
@[simp] theorem bank1 (b : Bank) (x y z w : Nat) : bank b x y z w 1 = y := by simp [bank]
@[simp] theorem bank9 (b : Bank) (x y z w : Nat) : bank b x y z w 9 = z := by simp [bank]
@[simp] theorem bank10 (b : Bank) (x y z w : Nat) : bank b x y z w 10 = w := by simp [bank]
@[simp] theorem bank_same (b : Bank) : bank b (b 4) (b 1) (b 9) (b 10) = b := by
  funext i; fin_cases i <;> simp [bank]

theorem write4 (b : Bank) (x y z w t : Nat) :
    write (bank b x y z w) 4 t = bank b t y z w := by
  funext i; fin_cases i <;> simp [bank, write]
theorem write1 (b : Bank) (x y z w t : Nat) :
    write (bank b x y z w) 1 t = bank b x t z w := by
  funext i; fin_cases i <;> simp [bank, write]
theorem write9 (b : Bank) (x y z w t : Nat) :
    write (bank b x y z w) 9 t = bank b x y t w := by
  funext i; fin_cases i <;> simp [bank, write]
theorem write10 (b : Bank) (x y z w t : Nat) :
    write (bank b x y z w) 10 t = bank b x y z t := by
  funext i; fin_cases i <;> simp [bank, write]

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem step124_zero (b : Bank) (y z w : Nat) :
    target.system.step ⟨124, bank b 0 y z w⟩ = ⟨⟨127, bank b 0 y z w⟩, []⟩ := by rfl
theorem step124_succ (b : Bank) (x y z w : Nat) :
    target.system.step ⟨124, bank b (x+1) y z w⟩ = ⟨⟨125, bank b x y z w⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write4]
theorem step125 (b : Bank) (x y z w : Nat) :
    target.system.step ⟨125, bank b x y z w⟩ = ⟨⟨126, bank b x y z (w+1)⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write10]
theorem step126 (b : Bank) (x y z w : Nat) :
    target.system.step ⟨126, bank b x y z w⟩ = ⟨⟨124, bank b x y (z+1) w⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write9]
theorem step127_zero (b : Bank) (x y w : Nat) :
    target.system.step ⟨127, bank b x y 0 w⟩ = ⟨⟨129, bank b x y 0 w⟩, []⟩ := by rfl
theorem step127_succ (b : Bank) (x y z w : Nat) :
    target.system.step ⟨127, bank b x y (z+1) w⟩ = ⟨⟨128, bank b x y z w⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write9]
theorem step128 (b : Bank) (x y z w : Nat) :
    target.system.step ⟨128, bank b x y z w⟩ = ⟨⟨127, bank b (x+1) y z w⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write4]
theorem step129_zero (b : Bank) (x z w : Nat) :
    target.system.step ⟨129, bank b x 0 z w⟩ = ⟨⟨130, bank b x 0 z w⟩, []⟩ := by rfl
theorem step129_succ (b : Bank) (x y z w : Nat) :
    target.system.step ⟨129, bank b x (y+1) z w⟩ = ⟨⟨129, bank b x y z w⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write1]
theorem step130_zero (b : Bank) (x y z : Nat) :
    target.system.step ⟨130, bank b x y z 0⟩ = ⟨⟨132, bank b x y z 0⟩, []⟩ := by rfl
theorem step130_succ (b : Bank) (x y z w : Nat) :
    target.system.step ⟨130, bank b x y z (w+1)⟩ = ⟨⟨131, bank b x y z w⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write10]
theorem step131 (b : Bank) (x y z w : Nat) :
    target.system.step ⟨131, bank b x y z w⟩ = ⟨⟨130, bank b x (y+1) z w⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write1]

theorem drain_three (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨124, bank b (x+1) y z w⟩ 3 = ⟨124, bank b x y (z+1) (w+1)⟩ ∧
    target.system.wordFrom ⟨124, bank b (x+1) y z w⟩ 3 = [] := by
  simp [WordEventSystem.advance, WordEventSystem.wordFrom, step124_succ, step125, step126]

theorem restore_two (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨127, bank b x y (z+1) w⟩ 2 = ⟨127, bank b (x+1) y z w⟩ ∧
    target.system.wordFrom ⟨127, bank b x y (z+1) w⟩ 2 = [] := by
  simp [WordEventSystem.advance, WordEventSystem.wordFrom, step127_succ, step128]

theorem place_two (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨130, bank b x y z (w+1)⟩ 2 = ⟨130, bank b x (y+1) z w⟩ ∧
    target.system.wordFrom ⟨130, bank b x y z (w+1)⟩ 2 = [] := by
  simp [WordEventSystem.advance, WordEventSystem.wordFrom, step130_succ, step131]

theorem drain (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨124, bank b x y z w⟩ (3*x+1) = ⟨127, bank b 0 y (z+x) (w+x)⟩ ∧
    target.system.wordFrom ⟨124, bank b x y z w⟩ (3*x+1) = [] := by
  induction x generalizing z w with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step124_zero]
  | succ x ih =>
    have hs := drain_three b x y z w
    have hi := ih (z+1) (w+1)
    have ht : 3*(x+1)+1 = 3 + (3*x+1) := by omega
    have hz : z+1+x = z+(x+1) := by omega
    have hw : w+1+x = w+(x+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add, hs.1, hi.1, hz, hw]
    · rw [ht, WordEventSystem.wordFrom_add, hs.1, hs.2, hi.2]; simp

theorem restore (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨127, bank b x y z w⟩ (2*z+1) = ⟨129, bank b (x+z) y 0 w⟩ ∧
    target.system.wordFrom ⟨127, bank b x y z w⟩ (2*z+1) = [] := by
  induction z generalizing x with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step127_zero]
  | succ z ih =>
    have hs := restore_two b x y z w
    have hi := ih (x+1)
    have ht : 2*(z+1)+1 = 2 + (2*z+1) := by omega
    have hx : x+1+z = x+(z+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add, hs.1, hi.1, hx]
    · rw [ht, WordEventSystem.wordFrom_add, hs.1, hs.2, hi.2]; simp

theorem clear (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨129, bank b x y z w⟩ (y+1) = ⟨130, bank b x 0 z w⟩ ∧
    target.system.wordFrom ⟨129, bank b x y z w⟩ (y+1) = [] := by
  induction y with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step129_zero]
  | succ y ih =>
    have hs := step129_succ b x y z w
    have ht : y+1+1 = 1+(y+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add]
      simpa [WordEventSystem.advance, hs] using ih.1
    · rw [ht, WordEventSystem.wordFrom_add]
      simpa [WordEventSystem.advance, WordEventSystem.wordFrom, hs] using ih.2

theorem place (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨130, bank b x y z w⟩ (2*w+1) = ⟨132, bank b x (y+w) z 0⟩ ∧
    target.system.wordFrom ⟨130, bank b x y z w⟩ (2*w+1) = [] := by
  induction w generalizing y with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step130_zero]
  | succ w ih =>
    have hs := place_two b x y z w
    have hi := ih (y+1)
    have ht : 2*(w+1)+1 = 2 + (2*w+1) := by omega
    have hy : y+1+w = y+(w+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add, hs.1, hi.1, hy]
    · rw [ht, WordEventSystem.wordFrom_add, hs.1, hs.2, hi.2]; simp


end Shared.Beeping.NPcoNP.Source284GraphCandidateInputCopy
