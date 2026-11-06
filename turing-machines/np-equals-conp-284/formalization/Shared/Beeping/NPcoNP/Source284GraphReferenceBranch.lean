import Shared.Beeping.NPcoNP.Parent290Coalesced

/-! The checked graph's reference-certificate loop entry. This module starts
from a supplied register bank; it does not prove physical reachability or the
correctness of the subsequent bounded evaluator. -/
namespace Shared.Beeping.NPcoNP.Source284GraphReferenceBranch

open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced

abbrev Bank := PASoundness.RegisterMachine.Bank 12

/-- The four mutable registers in the reference-loop setup. -/
def bank (b : Bank) (x y z w : Nat) : Bank :=
  fun i => if i = 7 then x else if i = 8 then y else if i = 9 then z else if i = 10 then w else b i

@[simp] theorem bank7 (b : Bank) (x y z w : Nat) : bank b x y z w 7 = x := by simp [bank]
@[simp] theorem bank8 (b : Bank) (x y z w : Nat) : bank b x y z w 8 = y := by simp [bank]
@[simp] theorem bank9 (b : Bank) (x y z w : Nat) : bank b x y z w 9 = z := by simp [bank]
@[simp] theorem bank10 (b : Bank) (x y z w : Nat) : bank b x y z w 10 = w := by simp [bank]
@[simp] theorem bank_same (b : Bank) : bank b (b 7) (b 8) (b 9) (b 10) = b := by
  funext i; fin_cases i <;> simp [bank]

theorem write7 (b : Bank) (x y z w t : Nat) :
    write (bank b x y z w) 7 t = bank b t y z w := by
  funext i; fin_cases i <;> simp [bank, write]
theorem write8 (b : Bank) (x y z w t : Nat) :
    write (bank b x y z w) 8 t = bank b x t z w := by
  funext i; fin_cases i <;> simp [bank, write]
theorem write9 (b : Bank) (x y z w t : Nat) :
    write (bank b x y z w) 9 t = bank b x y t w := by
  funext i; fin_cases i <;> simp [bank, write]
theorem write10 (b : Bank) (x y z w t : Nat) :
    write (bank b x y z w) 10 t = bank b x y z t := by
  funext i; fin_cases i <;> simp [bank, write]

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem step31_zero (b : Bank) (y z w : Nat) :
    target.system.step ⟨31, bank b 0 y z w⟩ = ⟨⟨89, bank b 0 y z w⟩, []⟩ := by rfl

theorem step31_succ (b : Bank) (x y z w : Nat) :
    target.system.step ⟨31, bank b (x+1) y z w⟩ = ⟨⟨32, bank b x y z w⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write7]

theorem step32_zero (b : Bank) (y z w : Nat) :
    target.system.step ⟨32, bank b 0 y z w⟩ = ⟨⟨35, bank b 0 y z w⟩, []⟩ := by rfl
theorem step32_succ (b : Bank) (x y z w : Nat) :
    target.system.step ⟨32, bank b (x+1) y z w⟩ = ⟨⟨33, bank b x y z w⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write7]
theorem step33 (b : Bank) (x y z w : Nat) :
    target.system.step ⟨33, bank b x y z w⟩ = ⟨⟨34, bank b x y z (w+1)⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write10]
theorem step34 (b : Bank) (x y z w : Nat) :
    target.system.step ⟨34, bank b x y z w⟩ = ⟨⟨32, bank b x y (z+1) w⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write9]
theorem step35_zero (b : Bank) (x y w : Nat) :
    target.system.step ⟨35, bank b x y 0 w⟩ = ⟨⟨37, bank b x y 0 w⟩, []⟩ := by rfl
theorem step35_succ (b : Bank) (x y z w : Nat) :
    target.system.step ⟨35, bank b x y (z+1) w⟩ = ⟨⟨36, bank b x y z w⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write9]
theorem step36 (b : Bank) (x y z w : Nat) :
    target.system.step ⟨36, bank b x y z w⟩ = ⟨⟨35, bank b (x+1) y z w⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write7]
theorem step37_zero (b : Bank) (x z w : Nat) :
    target.system.step ⟨37, bank b x 0 z w⟩ = ⟨⟨38, bank b x 0 z w⟩, []⟩ := by rfl
theorem step37_succ (b : Bank) (x y z w : Nat) :
    target.system.step ⟨37, bank b x (y+1) z w⟩ = ⟨⟨37, bank b x y z w⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write8]
theorem step38_zero (b : Bank) (x y z : Nat) :
    target.system.step ⟨38, bank b x y z 0⟩ = ⟨⟨40, bank b x y z 0⟩, []⟩ := by rfl
theorem step38_succ (b : Bank) (x y z w : Nat) :
    target.system.step ⟨38, bank b x y z (w+1)⟩ = ⟨⟨39, bank b x y z w⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write10]
theorem step39 (b : Bank) (x y z w : Nat) :
    target.system.step ⟨39, bank b x y z w⟩ = ⟨⟨38, bank b x (y+1) z w⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write8]

theorem drain_three (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨32, bank b (x+1) y z w⟩ 3 = ⟨32, bank b x y (z+1) (w+1)⟩ ∧
    target.system.wordFrom ⟨32, bank b (x+1) y z w⟩ 3 = [] := by
  simp [WordEventSystem.advance, WordEventSystem.wordFrom, step32_succ, step33, step34]

theorem restore_two (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨35, bank b x y (z+1) w⟩ 2 = ⟨35, bank b (x+1) y z w⟩ ∧
    target.system.wordFrom ⟨35, bank b x y (z+1) w⟩ 2 = [] := by
  simp [WordEventSystem.advance, WordEventSystem.wordFrom, step35_succ, step36]

theorem place_two (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨38, bank b x y z (w+1)⟩ 2 = ⟨38, bank b x (y+1) z w⟩ ∧
    target.system.wordFrom ⟨38, bank b x y z (w+1)⟩ 2 = [] := by
  simp [WordEventSystem.advance, WordEventSystem.wordFrom, step38_succ, step39]

theorem drain (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨32, bank b x y z w⟩ (3*x+1) = ⟨35, bank b 0 y (z+x) (w+x)⟩ ∧
    target.system.wordFrom ⟨32, bank b x y z w⟩ (3*x+1) = [] := by
  induction x generalizing z w with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step32_zero]
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
    target.system.advance ⟨35, bank b x y z w⟩ (2*z+1) = ⟨37, bank b (x+z) y 0 w⟩ ∧
    target.system.wordFrom ⟨35, bank b x y z w⟩ (2*z+1) = [] := by
  induction z generalizing x with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step35_zero]
  | succ z ih =>
    have hs := restore_two b x y z w
    have hi := ih (x+1)
    have ht : 2*(z+1)+1 = 2 + (2*z+1) := by omega
    have hx : x+1+z = x+(z+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add, hs.1, hi.1, hx]
    · rw [ht, WordEventSystem.wordFrom_add, hs.1, hs.2, hi.2]; simp

theorem clear (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨37, bank b x y z w⟩ (y+1) = ⟨38, bank b x 0 z w⟩ ∧
    target.system.wordFrom ⟨37, bank b x y z w⟩ (y+1) = [] := by
  induction y with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step37_zero]
  | succ y ih =>
    have hs := step37_succ b x y z w
    have ht : y+1+1 = 1+(y+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add]
      simpa [WordEventSystem.advance, hs] using ih.1
    · rw [ht, WordEventSystem.wordFrom_add]
      simpa [WordEventSystem.advance, WordEventSystem.wordFrom, hs] using ih.2

theorem place (b : Bank) (x y z w : Nat) :
    target.system.advance ⟨38, bank b x y z w⟩ (2*w+1) = ⟨40, bank b x (y+w) z 0⟩ ∧
    target.system.wordFrom ⟨38, bank b x y z w⟩ (2*w+1) = [] := by
  induction w generalizing y with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step38_zero]
  | succ w ih =>
    have hs := place_two b x y z w
    have hi := ih (y+1)
    have ht : 2*(w+1)+1 = 2 + (2*w+1) := by omega
    have hy : y+1+w = y+(w+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add, hs.1, hi.1, hy]
    · rw [ht, WordEventSystem.wordFrom_add, hs.1, hs.2, hi.2]; simp

def SilentSegment (a z : PASoundness.RegisterMachine.Config 12 185) (n : Nat) : Prop :=
  target.system.advance a n = z ∧ target.system.wordFrom a n = []

theorem cat {a b c : PASoundness.RegisterMachine.Config 12 185} {n m : Nat}
    (h : SilentSegment a b n) (g : SilentSegment b c m) : SilentSegment a c (n+m) := by
  rcases h with ⟨ha, hw⟩
  rcases g with ⟨ga, gw⟩
  constructor
  · rw [WordEventSystem.advance_add, ha, ga]
  · rw [WordEventSystem.wordFrom_add, ha, hw, gw]; rfl

/-- A nonempty certificate range performs one decrement, then copies the
remaining value into the candidate's initial left tape. -/
theorem branch_succ (b : Bank) (x y : Nat) :
    SilentSegment ⟨31, bank b (x+1) y 0 0⟩ ⟨40, bank b x x 0 0⟩ (7*x+y+5) := by
  have h₀ : SilentSegment ⟨31, bank b (x+1) y 0 0⟩ ⟨32, bank b x y 0 0⟩ 1 := by
    simp [SilentSegment, WordEventSystem.advance, WordEventSystem.wordFrom, step31_succ]
  have h₁ : SilentSegment ⟨32, bank b x y 0 0⟩ ⟨35, bank b 0 y x x⟩ (3*x+1) := by
    simpa [SilentSegment] using drain b x y 0 0
  have h₂ : SilentSegment ⟨35, bank b 0 y x x⟩ ⟨37, bank b x y 0 x⟩ (2*x+1) := by
    simpa [SilentSegment] using restore b 0 y x x
  have h₃ : SilentSegment ⟨37, bank b x y 0 x⟩ ⟨38, bank b x 0 0 x⟩ (y+1) := by
    simpa [SilentSegment] using clear b x y 0 x
  have h₄ : SilentSegment ⟨38, bank b x 0 0 x⟩ ⟨40, bank b x x 0 0⟩ (2*x+1) := by
    simpa [SilentSegment] using place b x 0 0 x
  have ht : 7*x+y+5 = (((1+(3*x+1))+(2*x+1))+(y+1))+(2*x+1) := by omega
  rw [ht]
  exact cat (cat (cat (cat h₀ h₁) h₂) h₃) h₄

/-- At a supplied PC 31 bank, a nonzero branch count is decremented and
copied to register 8. Both scratch registers must be zero at entry. -/
theorem branch_nonzero (b : Bank) (h : 0 < b 7) (h9 : b 9 = 0) (h10 : b 10 = 0) :
    let n := b 7 - 1
    let d := 7*n+b 8+5
    0 < d ∧ SilentSegment ⟨31,b⟩ ⟨40,bank b n n 0 0⟩ d := by
  dsimp
  constructor
  · omega
  · have hb : bank b ((b 7-1)+1) (b 8) 0 0 = b := by
      have hn : (b 7-1)+1 = b 7 := by omega
      simpa [hn, h9, h10] using bank_same b
    simpa only [hb] using branch_succ b (b 7-1) (b 8)

/-- An exhausted range immediately leaves the reference-search loop. -/
theorem branch_zero (b : Bank) (h : b 7 = 0) :
    SilentSegment ⟨31,b⟩ ⟨89,b⟩ 1 := by
  have hb : bank b 0 (b 8) (b 9) (b 10) = b := by
    rw [← h, bank_same]
  have hs := step31_zero b (b 8) (b 9) (b 10)
  rw [hb] at hs
  simp [SilentSegment, WordEventSystem.advance, WordEventSystem.wordFrom, hs]

end Shared.Beeping.NPcoNP.Source284GraphReferenceBranch
