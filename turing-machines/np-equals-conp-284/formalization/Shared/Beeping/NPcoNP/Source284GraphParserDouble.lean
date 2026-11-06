import Shared.Beeping.NPcoNP.Parent290Coalesced

/-! Literal coalesced graph rows 14–18: doubling the parser's accumulator.
This starts at a supplied graph configuration, not the blank physical tape. -/
namespace Shared.Beeping.NPcoNP.Source284GraphParserDouble
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP
open Shared.Beeping.NPcoNP.Parent290Coalesced

abbrev Bank := PASoundness.RegisterMachine.Bank 12
abbrev Cfg := PASoundness.RegisterMachine.Config 12 185

def bank (b : Bank) (x y : Nat) : Bank :=
  fun i => if i = 6 then x else if i = 10 then y else b i

@[simp] theorem bank_six (b : Bank) (x y : Nat) : bank b x y 6 = x := by simp [bank]
@[simp] theorem bank_ten (b : Bank) (x y : Nat) : bank b x y 10 = y := by simp [bank]
@[simp] theorem bank_same (b : Bank) : bank b (b 6) (b 10) = b := by
  funext i
  by_cases h : i = 6 <;> by_cases h' : i = 10 <;> simp [bank, h, h', *]

theorem write_six (b : Bank) (x y z : Nat) :
    write (bank b x y) 6 z = bank b z y := by
  funext i
  by_cases h : i = 6 <;> simp [write, bank, h]

theorem write_ten (b : Bank) (x y z : Nat) :
    write (bank b x y) 10 z = bank b x z := by
  funext i
  by_cases h : i = 6 <;> by_cases h' : i = 10 <;> simp [write, bank, h, h']

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem step14_positive (b : Bank) (x y : Nat) :
    target.system.step ⟨14, bank b (x+1) y⟩ = ⟨⟨15, bank b x y⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write_six]

theorem step14_zero (b : Bank) (y : Nat) :
    target.system.step ⟨14, bank b 0 y⟩ = ⟨⟨17, bank b 0 y⟩, []⟩ := by
  rfl

theorem step15 (b : Bank) (x y : Nat) :
    target.system.step ⟨15, bank b x y⟩ = ⟨⟨16, bank b x (y+1)⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write_ten]

theorem step16 (b : Bank) (x y : Nat) :
    target.system.step ⟨16, bank b x y⟩ = ⟨⟨14, bank b x (y+1)⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write_ten]

theorem step17_positive (b : Bank) (x y : Nat) :
    target.system.step ⟨17, bank b x (y+1)⟩ = ⟨⟨18, bank b x y⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write_ten]

theorem step17_zero (b : Bank) (x : Nat) :
    target.system.step ⟨17, bank b x 0⟩ = ⟨⟨19, bank b x 0⟩, []⟩ := by
  rfl

theorem step18 (b : Bank) (x y : Nat) :
    target.system.step ⟨18, bank b x y⟩ = ⟨⟨17, bank b (x+1) y⟩, []⟩ := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, write_six]

/-- One three-instruction transfer of an accumulator unit into two work units. -/
theorem transfer_three (b : Bank) (x y : Nat) :
    target.system.advance ⟨14, bank b (x+1) y⟩ 3 = ⟨14, bank b x (y+2)⟩ ∧
    target.system.wordFrom ⟨14, bank b (x+1) y⟩ 3 = [] := by
  simp [WordEventSystem.advance, WordEventSystem.wordFrom,
    step14_positive, step15, step16, Nat.add_assoc]

/-- One two-instruction return of a work unit to the accumulator. -/
theorem restore_two (b : Bank) (x y : Nat) :
    target.system.advance ⟨17, bank b x (y+1)⟩ 2 = ⟨17, bank b (x+1) y⟩ ∧
    target.system.wordFrom ⟨17, bank b x (y+1)⟩ 2 = [] := by
  simp [WordEventSystem.advance, WordEventSystem.wordFrom,
    step17_positive, step18]

/-- Drain accumulator into twice as much work, then move to the restore loop. -/
theorem transfer (b : Bank) (x y : Nat) :
    target.system.advance ⟨14, bank b x y⟩ (3*x+1) = ⟨17, bank b 0 (y+2*x)⟩ ∧
    target.system.wordFrom ⟨14, bank b x y⟩ (3*x+1) = [] := by
  induction x generalizing y with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step14_zero]
  | succ x ih =>
    have hs := transfer_three b x y
    have hi := ih (y+2)
    have ht : 3*(x+1)+1 = 3 + (3*x+1) := by omega
    have hv : y+2+2*x = y+2*(x+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add, hs.1, hi.1, hv]
    · rw [ht, WordEventSystem.wordFrom_add, hs.1, hs.2, hi.2]
      simp

/-- Drain the work register back into the accumulator. -/
theorem restore (b : Bank) (x y : Nat) :
    target.system.advance ⟨17, bank b x y⟩ (2*y+1) = ⟨19, bank b (x+y) 0⟩ ∧
    target.system.wordFrom ⟨17, bank b x y⟩ (2*y+1) = [] := by
  induction y generalizing x with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step17_zero]
  | succ y ih =>
    have hs := restore_two b x y
    have hi := ih (x+1)
    have ht : 2*(y+1)+1 = 2 + (2*y+1) := by omega
    have hv : x+1+y = x+(y+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add, hs.1, hi.1, hv]
    · rw [ht, WordEventSystem.wordFrom_add, hs.1, hs.2, hi.2]
      simp

/-- Positive finite silent doubling on the actual 185-row program, with the
work register zero on entry and exit, preserving every other register. -/
theorem double_segment (b : Bank) (hz : b 10 = 0) :
    let k := 7*b 6+2
    target.system.advance ⟨14,b⟩ k = ⟨19, write b 6 (2*b 6)⟩ ∧
    target.system.wordFrom ⟨14,b⟩ k = [] ∧ 0 < k := by
  have hb : bank b (b 6) 0 = b := by simpa [hz] using bank_same b
  have ht := transfer b (b 6) 0
  rw [hb] at ht
  simp only [Nat.zero_add] at ht
  have hr := restore b 0 (2*b 6)
  have hk : 7*b 6+2 = (3*b 6+1) + (2*(2*b 6)+1) := by omega
  have hout : bank b (2*b 6) 0 = write b 6 (2*b 6) := by
    rw [← write_six b (b 6) 0 (2*b 6), hb]
  dsimp only
  constructor
  · rw [hk, WordEventSystem.advance_add, ht.1]
    simpa [hout] using hr.1
  constructor
  · rw [hk, WordEventSystem.wordFrom_add, ht.1, ht.2, hr.2]
    rfl
  · omega

end Shared.Beeping.NPcoNP.Source284GraphParserDouble
