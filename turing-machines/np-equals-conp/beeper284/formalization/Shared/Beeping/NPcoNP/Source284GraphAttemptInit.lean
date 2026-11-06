import Shared.Beeping.NPcoNP.Source284GraphParserInit

/-! Literal graph initialization for a reference acceptance attempt. The
starting register bank is supplied; no blank-tape reachability is claimed. -/
namespace Shared.Beeping.NPcoNP.Source284GraphAttemptInit

open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphParserInit

abbrev B := PASoundness.RegisterMachine.Bank 12

def bank (b : B) (x y z w : Nat) : B :=
  fun i => if i = 5 then x else if i = 9 then y else if i = 10 then z else if i = 11 then w else b i

@[simp] theorem bank_five (b : B) (x y z w : Nat) : bank b x y z w 5 = x := by simp [bank]
@[simp] theorem bank_nine (b : B) (x y z w : Nat) : bank b x y z w 9 = y := by simp [bank]
@[simp] theorem bank_ten (b : B) (x y z w : Nat) : bank b x y z w 10 = z := by simp [bank]
@[simp] theorem bank_eleven (b : B) (x y z w : Nat) : bank b x y z w 11 = w := by simp [bank]
theorem bank_same (b : B) : bank b (b 5) (b 9) (b 10) (b 11) = b := by
  funext i
  fin_cases i <;> simp [bank]

theorem write_five (b : B) (x y z w a : Nat) : write (bank b x y z w) 5 a = bank b a y z w := by
  funext i; fin_cases i <;> simp [bank, write]
theorem write_nine (b : B) (x y z w a : Nat) : write (bank b x y z w) 9 a = bank b x a z w := by
  funext i; fin_cases i <;> simp [bank, write]
theorem write_ten (b : B) (x y z w a : Nat) : write (bank b x y z w) 10 a = bank b x y a w := by
  funext i; fin_cases i <;> simp [bank, write]
theorem write_eleven (b : B) (x y z w a : Nat) : write (bank b x y z w) 11 a = bank b x y z a := by
  funext i; fin_cases i <;> simp [bank, write]

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem row40 (b : B) : target.system.step ⟨40,b⟩ =
    if b 1 = 0 then (⟨41,b⟩, []) else (⟨40,write b 1 (b 1 - 1)⟩, []) := by
  cases h : b (1 : Fin 12) <;>
    simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute, h,
      Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
      CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix]

theorem row41 (b : B) : target.system.step ⟨41,b⟩ =
    if b 2 = 0 then (⟨42,b⟩, []) else (⟨41,write b 2 (b 2 - 1)⟩, []) := by
  cases h : b (2 : Fin 12) <;>
    simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute, h,
      Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
      CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix]

theorem row42 (b : B) : target.system.step ⟨42,b⟩ = (⟨43,write b 2 (b 2+1)⟩, []) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix]

theorem step43_positive (b : B) (x y z w : Nat) :
    target.system.step ⟨43,bank b (x+1) y z w⟩ = (⟨44,bank b x y z w⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write_five]
theorem step43_zero (b : B) (y z w : Nat) :
    target.system.step ⟨43,bank b 0 y z w⟩ = (⟨46,bank b 0 y z w⟩,[]) := by rfl
theorem step44 (b : B) (x y z w : Nat) :
    target.system.step ⟨44,bank b x y z w⟩ = (⟨45,bank b x y (z+1) w⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write_ten]
theorem step45 (b : B) (x y z w : Nat) :
    target.system.step ⟨45,bank b x y z w⟩ = (⟨43,bank b x (y+1) z w⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write_nine]
theorem step46_positive (b : B) (x y z w : Nat) :
    target.system.step ⟨46,bank b x (y+1) z w⟩ = (⟨47,bank b x y z w⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write_nine]
theorem step46_zero (b : B) (x z w : Nat) :
    target.system.step ⟨46,bank b x 0 z w⟩ = (⟨48,bank b x 0 z w⟩,[]) := by rfl
theorem step47 (b : B) (x y z w : Nat) :
    target.system.step ⟨47,bank b x y z w⟩ = (⟨46,bank b (x+1) y z w⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write_five]
theorem step48_positive (b : B) (x y z w : Nat) :
    target.system.step ⟨48,bank b x y (z+1) w⟩ = (⟨49,bank b x y z w⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write_ten]
theorem step48_zero (b : B) (x y w : Nat) :
    target.system.step ⟨48,bank b x y 0 w⟩ = (⟨50,bank b x y 0 w⟩,[]) := by rfl
theorem step49 (b : B) (x y z w : Nat) :
    target.system.step ⟨49,bank b x y z w⟩ = (⟨48,bank b x y z (w+1)⟩,[]) := by
  simp [target, MaskInvariant.Program.system, MaskInvariant.Action.execute, execute,
    Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, write_eleven]

/-- Drain register 5 into registers 9 and 10. -/
theorem copy_drain (b : B) (x y z w : Nat) :
    target.system.advance ⟨43,bank b x y z w⟩ (3*x+1) = ⟨46,bank b 0 (y+x) (z+x) w⟩ ∧
    target.system.wordFrom ⟨43,bank b x y z w⟩ (3*x+1) = [] := by
  induction x generalizing y z with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step43_zero]
  | succ x ih =>
    have hs : target.system.advance ⟨43,bank b (x+1) y z w⟩ 3 =
        ⟨43,bank b x (y+1) (z+1) w⟩ ∧
        target.system.wordFrom ⟨43,bank b (x+1) y z w⟩ 3 = [] := by
      simp [WordEventSystem.advance, WordEventSystem.wordFrom, step43_positive, step44, step45]
    have hi := ih (y+1) (z+1)
    have ht : 3*(x+1)+1 = 3+(3*x+1) := by omega
    have hy : y+1+x = y+(x+1) := by omega
    have hz : z+1+x = z+(x+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add, hs.1, hi.1, hy, hz]
    · rw [ht, WordEventSystem.wordFrom_add, hs.1, hs.2, hi.2]; simp

/-- Restore register 5 from register 9. -/
theorem copy_restore (b : B) (x y z w : Nat) :
    target.system.advance ⟨46,bank b x y z w⟩ (2*y+1) = ⟨48,bank b (x+y) 0 z w⟩ ∧
    target.system.wordFrom ⟨46,bank b x y z w⟩ (2*y+1) = [] := by
  induction y generalizing x with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step46_zero]
  | succ y ih =>
    have hs : target.system.advance ⟨46,bank b x (y+1) z w⟩ 2 =
        ⟨46,bank b (x+1) y z w⟩ ∧
        target.system.wordFrom ⟨46,bank b x (y+1) z w⟩ 2 = [] := by
      simp [WordEventSystem.advance, WordEventSystem.wordFrom, step46_positive, step47]
    have hi := ih (x+1)
    have ht : 2*(y+1)+1 = 2+(2*y+1) := by omega
    have hx : x+1+y = x+(y+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add, hs.1, hi.1, hx]
    · rw [ht, WordEventSystem.wordFrom_add, hs.1, hs.2, hi.2]; simp

/-- Drain register 10 into the step counter register 11. -/
theorem copy_finish (b : B) (x y z w : Nat) :
    target.system.advance ⟨48,bank b x y z w⟩ (2*z+1) = ⟨50,bank b x y 0 (w+z)⟩ ∧
    target.system.wordFrom ⟨48,bank b x y z w⟩ (2*z+1) = [] := by
  induction z generalizing w with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step48_zero]
  | succ z ih =>
    have hs : target.system.advance ⟨48,bank b x y (z+1) w⟩ 2 =
        ⟨48,bank b x y z (w+1)⟩ ∧
        target.system.wordFrom ⟨48,bank b x y (z+1) w⟩ 2 = [] := by
      simp [WordEventSystem.advance, WordEventSystem.wordFrom, step48_positive, step49]
    have hi := ih (w+1)
    have ht : 2*(z+1)+1 = 2+(2*z+1) := by omega
    have hw : w+1+z = w+(z+1) := by omega
    constructor
    · rw [ht, WordEventSystem.advance_add, hs.1, hi.1, hw]
    · rw [ht, WordEventSystem.wordFrom_add, hs.1, hs.2, hi.2]; simp

/-- The copy loop runs for arbitrary initial scratch values. -/
theorem copy_segment (b : B) (x y z w : Nat) :
    target.system.advance ⟨43,bank b x y z w⟩ (7*x+2*y+2*z+3) =
      ⟨50,bank b (y+x) 0 0 (w+(z+x))⟩ ∧
    target.system.wordFrom ⟨43,bank b x y z w⟩ (7*x+2*y+2*z+3) = [] := by
  have h1 := copy_drain b x y z w
  have h2 := copy_restore b 0 (y+x) (z+x) w
  have h3 := copy_finish b (y+x) 0 (z+x) w
  have ht : 7*x+2*y+2*z+3 = (3*x+1)+(2*(y+x)+1)+(2*(z+x)+1) := by omega
  have h12 : target.system.advance ⟨43,bank b x y z w⟩ ((3*x+1)+(2*(y+x)+1)) =
      ⟨48,bank b (y+x) 0 (z+x) w⟩ := by
    rw [WordEventSystem.advance_add, h1.1]
    simpa using h2.1
  have hw12 : target.system.wordFrom ⟨43,bank b x y z w⟩ ((3*x+1)+(2*(y+x)+1)) = [] := by
    rw [WordEventSystem.wordFrom_add, h1.1, h1.2, h2.2]
    rfl
  constructor
  · rw [ht, WordEventSystem.advance_add, h12, h3.1]
  · rw [ht, WordEventSystem.wordFrom_add, hw12, h12, h3.2]; rfl

/-- The literal graph clears the right tape and source state, initializes
state one, and copies the reference clock into register 11. All initial
scratch values are accounted for explicitly. -/
theorem attempt_init (b : B) :
    let d := b 1+b 2+7*b 5+2*b 9+2*b 10+6
    let start := write (write b 1 0) 2 1
    let out := bank start (b 9+b 5) 0 0 (b 11+(b 10+b 5))
    target.system.advance ⟨40,b⟩ d = ⟨50,out⟩ ∧
    target.system.wordFrom ⟨40,b⟩ d = [] ∧ 0 < d := by
  let b₁ := write b 1 0
  let b₂ := write b₁ 2 0
  let b₃ := write b₁ 2 1
  let c := 7*b 5+2*b 9+2*b 10+3
  have h1 := clear_loop target.system 40 41 1 row40 b
  have h2 := clear_loop target.system 41 42 2 row41 b₁
  have hb12 : b₁ 2 = b 2 := by simp [b₁,write]
  have h3 : target.system.advance ⟨42,b₂⟩ 1 = ⟨43,b₃⟩ ∧
      target.system.wordFrom ⟨42,b₂⟩ 1 = [] := by
    have hw : write b₂ 2 (b₂ 2 + 1) = b₃ := by
      funext i; fin_cases i <;> simp [b₁,b₂,b₃,write]
    constructor <;> simp [WordEventSystem.advance, WordEventSystem.wordFrom, row42, hw]
  have hc := copy_segment b₃ (b₃ 5) (b₃ 9) (b₃ 10) (b₃ 11)
  rw [bank_same] at hc
  have hv5 : b₃ 5 = b 5 := by simp [b₁,b₃,write]
  have hv9 : b₃ 9 = b 9 := by simp [b₁,b₃,write]
  have hv10 : b₃ 10 = b 10 := by simp [b₁,b₃,write]
  have hv11 : b₃ 11 = b 11 := by simp [b₁,b₃,write]
  rw [hv5,hv9,hv10,hv11] at hc
  have h12 : target.system.advance ⟨40,b⟩ ((b 1+1)+(b 2+1)) = ⟨42,b₂⟩ := by
    rw [WordEventSystem.advance_add, h1.1]
    simpa [hb12,b₂] using h2.1
  have hw12 : target.system.wordFrom ⟨40,b⟩ ((b 1+1)+(b 2+1)) = [] := by
    rw [WordEventSystem.wordFrom_add, h1.1, h1.2]
    simpa [hb12] using h2.2
  have h123 : target.system.advance ⟨40,b⟩ (((b 1+1)+(b 2+1))+1) = ⟨43,b₃⟩ := by
    rw [WordEventSystem.advance_add,h12,h3.1]
  have hw123 : target.system.wordFrom ⟨40,b⟩ (((b 1+1)+(b 2+1))+1) = [] := by
    rw [WordEventSystem.wordFrom_add,hw12,h12,h3.2]; rfl
  have ht : b 1+b 2+7*b 5+2*b 9+2*b 10+6 = (((b 1+1)+(b 2+1))+1)+c := by
    dsimp [c]; omega
  dsimp only
  constructor
  · rw [ht,WordEventSystem.advance_add,h123]; exact hc.1
  constructor
  · rw [ht,WordEventSystem.wordFrom_add,hw123,h123]; exact hc.2
  · omega

end Shared.Beeping.NPcoNP.Source284GraphAttemptInit
