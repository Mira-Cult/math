import Shared.Beeping.NPcoNP.Source284GraphReferenceAttempt

/-! A positive reference clock starts the first source-evaluator iteration
in the checked 12-register graph. This concerns supplied graph configurations,
not physical blank-tape reachability or a complete evaluator simulation. -/
namespace Shared.Beeping.NPcoNP.Source284GraphFirstIteration
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced

abbrev Bank := PASoundness.RegisterMachine.Bank 12

def bank (b : Bank) (s x y z t : Nat) : Bank :=
  fun i => if i = 2 then s else if i = 6 then x else if i = 9 then y else
    if i = 10 then z else if i = 11 then t else b i

@[simp] theorem bank2 (b : Bank) (s x y z t : Nat) : bank b s x y z t 2 = s := by simp [bank]
@[simp] theorem bank6 (b : Bank) (s x y z t : Nat) : bank b s x y z t 6 = x := by simp [bank]
@[simp] theorem bank9 (b : Bank) (s x y z t : Nat) : bank b s x y z t 9 = y := by simp [bank]
@[simp] theorem bank10 (b : Bank) (s x y z t : Nat) : bank b s x y z t 10 = z := by simp [bank]
@[simp] theorem bank11 (b : Bank) (s x y z t : Nat) : bank b s x y z t 11 = t := by simp [bank]
@[simp] theorem bank1 (b : Bank) (s x y z t : Nat) : bank b s x y z t 1 = b 1 := by simp [bank]
theorem bank_same (b : Bank) : bank b (b 2) (b 6) (b 9) (b 10) (b 11) = b := by
  funext i; fin_cases i <;> simp [bank]

theorem write2 (b : Bank) (s x y z t a : Nat) : write (bank b s x y z t) 2 a = bank b a x y z t := by
  funext i; fin_cases i <;> simp [bank, write]
theorem write6 (b : Bank) (s x y z t a : Nat) : write (bank b s x y z t) 6 a = bank b s a y z t := by
  funext i; fin_cases i <;> simp [bank, write]
theorem write9 (b : Bank) (s x y z t a : Nat) : write (bank b s x y z t) 9 a = bank b s x a z t := by
  funext i; fin_cases i <;> simp [bank, write]
theorem write10 (b : Bank) (s x y z t a : Nat) : write (bank b s x y z t) 10 a = bank b s x y a t := by
  funext i; fin_cases i <;> simp [bank, write]
theorem write11 (b : Bank) (s x y z t a : Nat) : write (bank b s x y z t) 11 a = bank b s x y z a := by
  funext i; fin_cases i <;> simp [bank, write]

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem row50_positive (b : Bank) (s x y z t : Nat) :
    target.system.step ⟨50,bank b s x y z (t+1)⟩ = (⟨51,bank b s x y z t⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write11]
theorem row51_positive (b : Bank) (s x y z t : Nat) :
    target.system.step ⟨51,bank b (s+1) x y z t⟩ = (⟨52,bank b s x y z t⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write2]
theorem row52_zero (b : Bank) (s x y z t : Nat) (h : b 1 = 0) :
    target.system.step ⟨52,bank b s x y z t⟩ = (⟨54,bank b s x y z t⟩,[]) := by
  have hw : write (bank b s x y z t) 1 0 = bank b s x y z t := by
    funext i
    by_cases hi : i = 1
    · subst i; simp [write, bank, h]
    · simp [write, hi]
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, h, hw]
theorem row54_positive (b : Bank) (s x y z t : Nat) :
    target.system.step ⟨54,bank b s (x+1) y z t⟩ = (⟨55,bank b s x y z t⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write6]
theorem row54_zero (b : Bank) (s y z t : Nat) :
    target.system.step ⟨54,bank b s 0 y z t⟩ = (⟨57,bank b s 0 y z t⟩,[]) := by rfl
theorem row55 (b : Bank) (s x y z t : Nat) :
    target.system.step ⟨55,bank b s x y z t⟩ = (⟨56,bank b s x y (z+1) t⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write10]
theorem row56 (b : Bank) (s x y z t : Nat) :
    target.system.step ⟨56,bank b s x y z t⟩ = (⟨54,bank b s x (y+1) z t⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write9]
theorem row57_positive (b : Bank) (s x y z t : Nat) :
    target.system.step ⟨57,bank b s x (y+1) z t⟩ = (⟨58,bank b s x y z t⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write9]
theorem row57_zero (b : Bank) (s x z t : Nat) :
    target.system.step ⟨57,bank b s x 0 z t⟩ = (⟨59,bank b s x 0 z t⟩,[]) := by rfl
theorem row58 (b : Bank) (s x y z t : Nat) :
    target.system.step ⟨58,bank b s x y z t⟩ = (⟨57,bank b s (x+1) y z t⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write6]
theorem row59_zero (b : Bank) (s x z t : Nat) :
    target.system.step ⟨59,bank b s x 0 z t⟩ = (⟨60,bank b s x 0 z t⟩,[]) := by rfl

/-- Copy register 6 into scratch registers 9 and 10. -/
theorem drain (b : Bank) (s x y z t : Nat) :
    target.system.advance ⟨54,bank b s x y z t⟩ (3*x+1) = ⟨57,bank b s 0 (y+x) (z+x) t⟩ ∧
    target.system.wordFrom ⟨54,bank b s x y z t⟩ (3*x+1) = [] := by
  induction x generalizing y z with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, row54_zero]
  | succ x ih =>
    have hs : target.system.advance ⟨54,bank b s (x+1) y z t⟩ 3 =
        ⟨54,bank b s x (y+1) (z+1) t⟩ ∧
        target.system.wordFrom ⟨54,bank b s (x+1) y z t⟩ 3 = [] := by
      simp [WordEventSystem.advance, WordEventSystem.wordFrom, row54_positive, row55, row56]
    have hi := ih (y+1) (z+1)
    have ht : 3*(x+1)+1 = 3+(3*x+1) := by omega
    have hy : y+1+x = y+(x+1) := by omega
    have hz : z+1+x = z+(x+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add, hs.1, hi.1, hy, hz]
    · rw [ht, WordEventSystem.wordFrom_add, hs.1, hs.2, hi.2]; simp

/-- Restore register 6 from register 9. -/
theorem restore (b : Bank) (s x y z t : Nat) :
    target.system.advance ⟨57,bank b s x y z t⟩ (2*y+1) = ⟨59,bank b s (x+y) 0 z t⟩ ∧
    target.system.wordFrom ⟨57,bank b s x y z t⟩ (2*y+1) = [] := by
  induction y generalizing x with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, row57_zero]
  | succ y ih =>
    have hs : target.system.advance ⟨57,bank b s x (y+1) z t⟩ 2 =
        ⟨57,bank b s (x+1) y z t⟩ ∧
        target.system.wordFrom ⟨57,bank b s x (y+1) z t⟩ 2 = [] := by
      simp [WordEventSystem.advance, WordEventSystem.wordFrom, row57_positive, row58]
    have hi := ih (x+1)
    have ht : 2*(y+1)+1 = 2+(2*y+1) := by omega
    have hx : x+1+y = x+(y+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add, hs.1, hi.1, hx]
    · rw [ht, WordEventSystem.wordFrom_add, hs.1, hs.2, hi.2]; simp

/-- The zero-right-half first iteration dispatches to record lookup after
exactly `5*x+6` silent register-graph steps, preserving the source clock
minus one. The source state must initially be one and both scratch counters
must be zero. -/
theorem first_iteration (b : Bank) (x t : Nat) (h : b 1 = 0) :
    target.system.advance ⟨50,bank b 1 x 0 0 (t+1)⟩ (5*x+6) =
      ⟨60,bank b 0 x 0 x t⟩ ∧
    target.system.wordFrom ⟨50,bank b 1 x 0 0 (t+1)⟩ (5*x+6) = [] := by
  have hstart : target.system.advance ⟨50,bank b 1 x 0 0 (t+1)⟩ 3 =
      ⟨54,bank b 0 x 0 0 t⟩ ∧
      target.system.wordFrom ⟨50,bank b 1 x 0 0 (t+1)⟩ 3 = [] := by
    simp [WordEventSystem.advance, WordEventSystem.wordFrom, row50_positive,
      row51_positive, row52_zero, h]
  have hd := drain b 0 x 0 0 t
  have hr := restore b 0 0 x x t
  have he : target.system.advance ⟨59,bank b 0 x 0 x t⟩ 1 =
      ⟨60,bank b 0 x 0 x t⟩ ∧
      target.system.wordFrom ⟨59,bank b 0 x 0 x t⟩ 1 = [] := by
    simp [WordEventSystem.advance, WordEventSystem.wordFrom, row59_zero]
  have ht : 5*x+6 = (3+(3*x+1))+(2*x+1)+1 := by omega
  have h12 : target.system.advance ⟨50,bank b 1 x 0 0 (t+1)⟩ (3+(3*x+1)) =
      ⟨57,bank b 0 0 x x t⟩ := by
    rw [WordEventSystem.advance_add,hstart.1]; simpa using hd.1
  have hw12 : target.system.wordFrom ⟨50,bank b 1 x 0 0 (t+1)⟩ (3+(3*x+1)) = [] := by
    rw [WordEventSystem.wordFrom_add,hstart.1,hstart.2]; simpa using hd.2
  have h123 : target.system.advance ⟨50,bank b 1 x 0 0 (t+1)⟩ ((3+(3*x+1))+(2*x+1)) =
      ⟨59,bank b 0 x 0 x t⟩ := by
    rw [WordEventSystem.advance_add,h12]; simpa using hr.1
  have hw123 : target.system.wordFrom ⟨50,bank b 1 x 0 0 (t+1)⟩ ((3+(3*x+1))+(2*x+1)) = [] := by
    rw [WordEventSystem.wordFrom_add,h12,hw12]; simpa using hr.2
  constructor
  · rw [ht,WordEventSystem.advance_add,h123,he.1]
  · rw [ht,WordEventSystem.wordFrom_add,h123,hw123,he.2]; rfl

/-- The previous reference-attempt setup meets the first-iteration interface
when the reference clock is positive and both scratch registers are zero. -/
theorem ready_first_iteration (b : Bank) (h5 : 0 < b 5)
    (h9 : b 9 = 0) (h10 : b 10 = 0) :
    let r := Source284GraphReferenceAttempt.ready b
    target.system.advance ⟨50,r⟩ (5*b 6+6) =
      ⟨60,bank r 0 (b 6) 0 (b 6) (b 5-1)⟩ ∧
    target.system.wordFrom ⟨50,r⟩ (5*b 6+6) = [] := by
  let r := Source284GraphReferenceAttempt.ready b
  have hr1 : r 1 = 0 := by simp [r, Source284GraphReferenceAttempt.ready, write]
  have hr2 : r 2 = 1 := by simp [r, Source284GraphReferenceAttempt.ready, write]
  have hr6 : r 6 = b 6 := by simp [r, Source284GraphReferenceAttempt.ready, write]
  have hr9 : r 9 = 0 := by simp [r, Source284GraphReferenceAttempt.ready, write, h9]
  have hr10 : r 10 = 0 := by simp [r, Source284GraphReferenceAttempt.ready, write, h10]
  have hr11 : r 11 = b 5 := by simp [r, Source284GraphReferenceAttempt.ready, write]
  have ht : b 5 - 1 + 1 = b 5 := by omega
  have hb : bank r 1 (b 6) 0 0 (b 5) = r := by
    calc
      bank r 1 (b 6) 0 0 (b 5) = bank r (r 2) (r 6) (r 9) (r 10) (r 11) := by
        rw [hr2,hr6,hr9,hr10,hr11]
      _ = r := bank_same r
  have hf := first_iteration r (b 6) (b 5-1) hr1
  rw [ht,hb] at hf
  exact hf

end Shared.Beeping.NPcoNP.Source284GraphFirstIteration
