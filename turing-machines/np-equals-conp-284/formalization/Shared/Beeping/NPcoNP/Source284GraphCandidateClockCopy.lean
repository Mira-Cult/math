import Shared.Beeping.NPcoNP.Source284GraphParserInit

/-! Literal graph initialization for a candidate clock-copy block. The
starting register bank is supplied; no blank-tape reachability is claimed. -/
namespace Shared.Beeping.NPcoNP.Source284GraphCandidateClockCopy

open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphParserInit

abbrev B := PASoundness.RegisterMachine.Bank 12

def bank (b : B) (x y z w : Nat) : B :=
  fun i => if i = 6 then x else if i = 9 then y else if i = 10 then z else if i = 11 then w else b i

@[simp] theorem bank_six (b : B) (x y z w : Nat) : bank b x y z w 6 = x := by simp [bank]
@[simp] theorem bank_nine (b : B) (x y z w : Nat) : bank b x y z w 9 = y := by simp [bank]
@[simp] theorem bank_ten (b : B) (x y z w : Nat) : bank b x y z w 10 = z := by simp [bank]
@[simp] theorem bank_eleven (b : B) (x y z w : Nat) : bank b x y z w 11 = w := by simp [bank]
theorem bank_same (b : B) : bank b (b 6) (b 9) (b 10) (b 11) = b := by
  funext i
  fin_cases i <;> simp [bank]

theorem write_six (b : B) (x y z w a : Nat) : write (bank b x y z w) 6 a = bank b a y z w := by
  funext i; fin_cases i <;> simp [bank, write]
theorem write_nine (b : B) (x y z w a : Nat) : write (bank b x y z w) 9 a = bank b x a z w := by
  funext i; fin_cases i <;> simp [bank, write]
theorem write_ten (b : B) (x y z w a : Nat) : write (bank b x y z w) 10 a = bank b x y a w := by
  funext i; fin_cases i <;> simp [bank, write]
theorem write_eleven (b : B) (x y z w a : Nat) : write (bank b x y z w) 11 a = bank b x y z a := by
  funext i; fin_cases i <;> simp [bank, write]

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem step134_positive (b : B) (x y z w : Nat) :
    target.system.step ⟨134,bank b (x+1) y z w⟩ = (⟨135,bank b x y z w⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write_six]
theorem step134_zero (b : B) (y z w : Nat) :
    target.system.step ⟨134,bank b 0 y z w⟩ = (⟨137,bank b 0 y z w⟩,[]) := by rfl
theorem step135 (b : B) (x y z w : Nat) :
    target.system.step ⟨135,bank b x y z w⟩ = (⟨136,bank b x y (z+1) w⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write_ten]
theorem step136 (b : B) (x y z w : Nat) :
    target.system.step ⟨136,bank b x y z w⟩ = (⟨134,bank b x (y+1) z w⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write_nine]
theorem step137_positive (b : B) (x y z w : Nat) :
    target.system.step ⟨137,bank b x (y+1) z w⟩ = (⟨138,bank b x y z w⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write_nine]
theorem step137_zero (b : B) (x z w : Nat) :
    target.system.step ⟨137,bank b x 0 z w⟩ = (⟨139,bank b x 0 z w⟩,[]) := by rfl
theorem step138 (b : B) (x y z w : Nat) :
    target.system.step ⟨138,bank b x y z w⟩ = (⟨137,bank b (x+1) y z w⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write_six]
theorem step139_positive (b : B) (x y z w : Nat) :
    target.system.step ⟨139,bank b x y (z+1) w⟩ = (⟨140,bank b x y z w⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write_ten]
theorem step139_zero (b : B) (x y w : Nat) :
    target.system.step ⟨139,bank b x y 0 w⟩ = (⟨141,bank b x y 0 w⟩,[]) := by rfl
theorem step140 (b : B) (x y z w : Nat) :
    target.system.step ⟨140,bank b x y z w⟩ = (⟨139,bank b x y z (w+1)⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write_eleven]

/-- Drain register 6 into registers 9 and 10. -/
theorem copy_drain (b : B) (x y z w : Nat) :
    target.system.advance ⟨134,bank b x y z w⟩ (3*x+1) = ⟨137,bank b 0 (y+x) (z+x) w⟩ ∧
    target.system.wordFrom ⟨134,bank b x y z w⟩ (3*x+1) = [] := by
  induction x generalizing y z with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step134_zero]
  | succ x ih =>
    have hs : target.system.advance ⟨134,bank b (x+1) y z w⟩ 3 =
        ⟨134,bank b x (y+1) (z+1) w⟩ ∧
        target.system.wordFrom ⟨134,bank b (x+1) y z w⟩ 3 = [] := by
      simp [WordEventSystem.advance, WordEventSystem.wordFrom, step134_positive, step135, step136]
    have hi := ih (y+1) (z+1)
    have ht : 3*(x+1)+1 = 3+(3*x+1) := by omega
    have hy : y+1+x = y+(x+1) := by omega
    have hz : z+1+x = z+(x+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add, hs.1, hi.1, hy, hz]
    · rw [ht, WordEventSystem.wordFrom_add, hs.1, hs.2, hi.2]; simp

/-- Restore register 6 from register 9. -/
theorem copy_restore (b : B) (x y z w : Nat) :
    target.system.advance ⟨137,bank b x y z w⟩ (2*y+1) = ⟨139,bank b (x+y) 0 z w⟩ ∧
    target.system.wordFrom ⟨137,bank b x y z w⟩ (2*y+1) = [] := by
  induction y generalizing x with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step137_zero]
  | succ y ih =>
    have hs : target.system.advance ⟨137,bank b x (y+1) z w⟩ 2 =
        ⟨137,bank b (x+1) y z w⟩ ∧
        target.system.wordFrom ⟨137,bank b x (y+1) z w⟩ 2 = [] := by
      simp [WordEventSystem.advance, WordEventSystem.wordFrom, step137_positive, step138]
    have hi := ih (x+1)
    have ht : 2*(y+1)+1 = 2+(2*y+1) := by omega
    have hx : x+1+y = x+(y+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add, hs.1, hi.1, hx]
    · rw [ht, WordEventSystem.wordFrom_add, hs.1, hs.2, hi.2]; simp

/-- Drain register 10 into the step counter register 11. -/
theorem copy_finish (b : B) (x y z w : Nat) :
    target.system.advance ⟨139,bank b x y z w⟩ (2*z+1) = ⟨141,bank b x y 0 (w+z)⟩ ∧
    target.system.wordFrom ⟨139,bank b x y z w⟩ (2*z+1) = [] := by
  induction z generalizing w with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step139_zero]
  | succ z ih =>
    have hs : target.system.advance ⟨139,bank b x y (z+1) w⟩ 2 =
        ⟨139,bank b x y z (w+1)⟩ ∧
        target.system.wordFrom ⟨139,bank b x y (z+1) w⟩ 2 = [] := by
      simp [WordEventSystem.advance, WordEventSystem.wordFrom, step139_positive, step140]
    have hi := ih (w+1)
    have ht : 2*(z+1)+1 = 2+(2*z+1) := by omega
    have hw : w+1+z = w+(z+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add, hs.1, hi.1, hw]
    · rw [ht, WordEventSystem.wordFrom_add, hs.1, hs.2, hi.2]; simp

/-- The copy loop runs for arbitrary initial scratch values. -/
theorem copy_segment (b : B) (x y z w : Nat) :
    target.system.advance ⟨134,bank b x y z w⟩ (7*x+2*y+2*z+3) =
      ⟨141,bank b (y+x) 0 0 (w+(z+x))⟩ ∧
    target.system.wordFrom ⟨134,bank b x y z w⟩ (7*x+2*y+2*z+3) = [] := by
  have h1 := copy_drain b x y z w
  have h2 := copy_restore b 0 (y+x) (z+x) w
  have h3 := copy_finish b (y+x) 0 (z+x) w
  have ht : 7*x+2*y+2*z+3 = (3*x+1)+(2*(y+x)+1)+(2*(z+x)+1) := by omega
  have h12 : target.system.advance ⟨134,bank b x y z w⟩ ((3*x+1)+(2*(y+x)+1)) =
      ⟨139,bank b (y+x) 0 (z+x) w⟩ := by
    rw [WordEventSystem.advance_add, h1.1]
    simpa using h2.1
  have hw12 : target.system.wordFrom ⟨134,bank b x y z w⟩ ((3*x+1)+(2*(y+x)+1)) = [] := by
    rw [WordEventSystem.wordFrom_add, h1.1, h1.2, h2.2]
    rfl
  constructor
  · rw [ht, WordEventSystem.advance_add, h12, h3.1]
  · rw [ht, WordEventSystem.wordFrom_add, hw12, h12, h3.2]; rfl


end Shared.Beeping.NPcoNP.Source284GraphCandidateClockCopy
