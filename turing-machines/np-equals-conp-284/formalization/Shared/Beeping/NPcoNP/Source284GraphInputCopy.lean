import Shared.Beeping.NPcoNP.Source284GraphParserInit

/-! Exact graph-level copy of the complete candidate input. The supplied
PC-2 configuration must have both temporary registers zero; this theorem
does not establish that configuration's reachability from blank tape. -/
namespace Shared.Beeping.NPcoNP.Source284GraphInputCopy
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphParserInit (clear_loop)

abbrev Bank := PASoundness.RegisterMachine.Bank 12

def bank (b : Bank) (w x y z : Nat) : Bank :=
  fun i => if i = 0 then w else if i = 4 then x else if i = 9 then y else if i = 10 then z else b i

@[simp] theorem bank_zero (b : Bank) (w x y z : Nat) : bank b w x y z 0 = w := by simp [bank]
@[simp] theorem bank_four (b : Bank) (w x y z : Nat) : bank b w x y z 4 = x := by simp [bank]
@[simp] theorem bank_nine (b : Bank) (w x y z : Nat) : bank b w x y z 9 = y := by simp [bank]
@[simp] theorem bank_ten (b : Bank) (w x y z : Nat) : bank b w x y z 10 = z := by simp [bank]
@[simp] theorem bank_same (b : Bank) : bank b (b 0) (b 4) (b 9) (b 10) = b := by
  funext i
  by_cases h0 : i = 0 <;> by_cases h4 : i = 4 <;> by_cases h9 : i = 9 <;>
    by_cases h10 : i = 10 <;> simp [bank, h0, h4, h9, h10, *]

theorem write_zero (b : Bank) (w x y z v : Nat) :
    write (bank b w x y z) 0 v = bank b v x y z := by
  funext i; by_cases h : i = 0 <;> simp [write, bank, h]
theorem write_four (b : Bank) (w x y z v : Nat) :
    write (bank b w x y z) 4 v = bank b w v y z := by
  funext i; by_cases h0 : i = 0 <;> by_cases h4 : i = 4 <;> simp [write, bank, h0, h4]
theorem write_nine (b : Bank) (w x y z v : Nat) :
    write (bank b w x y z) 9 v = bank b w x v z := by
  funext i; by_cases h0 : i = 0 <;> by_cases h4 : i = 4 <;> by_cases h9 : i = 9 <;> simp [write, bank, h0, h4, h9]
theorem write_ten (b : Bank) (w x y z v : Nat) :
    write (bank b w x y z) 10 v = bank b w x y v := by
  funext i; by_cases h0 : i = 0 <;> by_cases h4 : i = 4 <;> by_cases h9 : i = 9 <;> by_cases h10 : i = 10 <;> simp [write, bank, h0, h4, h9, h10]

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

macro "row_simp" : tactic => `(tactic| simp [target, MaskInvariant.Program.system,
  MaskInvariant.Action.execute, Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
  CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix,
  PASoundness.RegisterMachine.execute, write_zero, write_four, write_nine, write_ten])

theorem step2_positive (b : Bank) (w x y z : Nat) :
    target.system.step ⟨2,bank b w (x+1) y z⟩ = (⟨3,bank b w x y z⟩,[]) := by row_simp
theorem step2_zero (b : Bank) (w y z : Nat) :
    target.system.step ⟨2,bank b w 0 y z⟩ = (⟨5,bank b w 0 y z⟩,[]) := by rfl
theorem step3 (b : Bank) (w x y z : Nat) :
    target.system.step ⟨3,bank b w x y z⟩ = (⟨4,bank b w x y (z+1)⟩,[]) := by row_simp
theorem step4 (b : Bank) (w x y z : Nat) :
    target.system.step ⟨4,bank b w x y z⟩ = (⟨2,bank b w x (y+1) z⟩,[]) := by row_simp
theorem step5_positive (b : Bank) (w x y z : Nat) :
    target.system.step ⟨5,bank b w x (y+1) z⟩ = (⟨6,bank b w x y z⟩,[]) := by row_simp
theorem step5_zero (b : Bank) (w x z : Nat) :
    target.system.step ⟨5,bank b w x 0 z⟩ = (⟨7,bank b w x 0 z⟩,[]) := by rfl
theorem step6 (b : Bank) (w x y z : Nat) :
    target.system.step ⟨6,bank b w x y z⟩ = (⟨5,bank b w (x+1) y z⟩,[]) := by row_simp
theorem step8_positive (b : Bank) (w x y z : Nat) :
    target.system.step ⟨8,bank b w x y (z+1)⟩ = (⟨9,bank b w x y z⟩,[]) := by row_simp
theorem step8_zero (b : Bank) (w x y : Nat) :
    target.system.step ⟨8,bank b w x y 0⟩ = (⟨10,bank b w x y 0⟩,[]) := by rfl
theorem step9 (b : Bank) (w x y z : Nat) :
    target.system.step ⟨9,bank b w x y z⟩ = (⟨8,bank b (w+1) x y z⟩,[]) := by row_simp

theorem transfer (b : Bank) (w x y z : Nat) :
    target.system.advance ⟨2,bank b w x y z⟩ (3*x+1) = ⟨5,bank b w 0 (y+x) (z+x)⟩ ∧
    target.system.wordFrom ⟨2,bank b w x y z⟩ (3*x+1) = [] := by
  induction x generalizing y z with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step2_zero]
  | succ x ih =>
    have hs : target.system.advance ⟨2,bank b w (x+1) y z⟩ 3 = ⟨2,bank b w x (y+1) (z+1)⟩ ∧
        target.system.wordFrom ⟨2,bank b w (x+1) y z⟩ 3 = [] := by
      simp [WordEventSystem.advance, WordEventSystem.wordFrom, step2_positive, step3, step4]
    have h := ih (y+1) (z+1)
    have hk : 3*(x+1)+1 = 3+(3*x+1) := by omega
    have hy : y+1+x = y+(x+1) := by omega
    have hz : z+1+x = z+(x+1) := by omega
    constructor
    · rw [hk, WordEventSystem.advance_add, hs.1, h.1, hy, hz]
    · rw [hk, WordEventSystem.wordFrom_add, hs.1, hs.2, h.2]; simp

theorem restore (b : Bank) (w x y z : Nat) :
    target.system.advance ⟨5,bank b w x y z⟩ (2*y+1) = ⟨7,bank b w (x+y) 0 z⟩ ∧
    target.system.wordFrom ⟨5,bank b w x y z⟩ (2*y+1) = [] := by
  induction y generalizing x with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step5_zero]
  | succ y ih =>
    have hs : target.system.advance ⟨5,bank b w x (y+1) z⟩ 2 = ⟨5,bank b w (x+1) y z⟩ ∧
        target.system.wordFrom ⟨5,bank b w x (y+1) z⟩ 2 = [] := by
      simp [WordEventSystem.advance, WordEventSystem.wordFrom, step5_positive, step6]
    have h := ih (x+1)
    have hk : 2*(y+1)+1 = 2+(2*y+1) := by omega
    have hx : x+1+y = x+(y+1) := by omega
    constructor
    · rw [hk, WordEventSystem.advance_add, hs.1, h.1, hx]
    · rw [hk, WordEventSystem.wordFrom_add, hs.1, hs.2, h.2]; simp

theorem move_work (b : Bank) (w x y z : Nat) :
    target.system.advance ⟨8,bank b w x y z⟩ (2*z+1) = ⟨10,bank b (w+z) x y 0⟩ ∧
    target.system.wordFrom ⟨8,bank b w x y z⟩ (2*z+1) = [] := by
  induction z generalizing w with
  | zero => simp [WordEventSystem.advance, WordEventSystem.wordFrom, step8_zero]
  | succ z ih =>
    have hs : target.system.advance ⟨8,bank b w x y (z+1)⟩ 2 = ⟨8,bank b (w+1) x y z⟩ ∧
        target.system.wordFrom ⟨8,bank b w x y (z+1)⟩ 2 = [] := by
      simp [WordEventSystem.advance, WordEventSystem.wordFrom, step8_positive, step9]
    have h := ih (w+1)
    have hk : 2*(z+1)+1 = 2+(2*z+1) := by omega
    have hw : w+1+z = w+(z+1) := by omega
    constructor
    · rw [hk, WordEventSystem.advance_add, hs.1, h.1, hw]
    · rw [hk, WordEventSystem.wordFrom_add, hs.1, hs.2, h.2]; simp

theorem row7 (b : Bank) : target.system.step ⟨7,b⟩ =
    if b 0 = 0 then (⟨8,b⟩, []) else (⟨7,write b 0 (b 0-1)⟩, []) := by
  cases h : b 0 <;> simp [target, MaskInvariant.Program.system,
    MaskInvariant.Action.execute, Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
    CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix, PASoundness.RegisterMachine.execute, h]

theorem compose {a b c : PASoundness.RegisterMachine.Config 12 185} {k l : Nat}
    (h : target.system.advance a k = b ∧ target.system.wordFrom a k = [])
    (g : target.system.advance b l = c ∧ target.system.wordFrom b l = []) :
    target.system.advance a (k+l) = c ∧ target.system.wordFrom a (k+l) = [] := by
  constructor
  · rw [WordEventSystem.advance_add, h.1, g.1]
  · rw [WordEventSystem.wordFrom_add, h.1, h.2, g.2]; rfl

/-- The checked graph copies the entire natural input in register 4 into
register 0, preserving register 4 and every other non-scratch register. -/
theorem input_copy (b : Bank) (h9 : b 9 = 0) (h10 : b 10 = 0) :
    let k := 7*b 4 + b 0 + 4
    target.system.advance ⟨2,b⟩ k = ⟨10,write b 0 (b 4)⟩ ∧
    target.system.wordFrom ⟨2,b⟩ k = [] ∧ 0 < k := by
  let x := b 4
  let w := b 0
  have hb : bank b w x 0 0 = b := by simpa [w,x,h9,h10] using bank_same b
  have ht := transfer b w x 0 0
  rw [hb] at ht
  simp only [Nat.zero_add] at ht
  have hr := restore b w 0 x x
  simp only [Nat.zero_add] at hr
  have hc := clear_loop target.system 7 8 0 row7 (bank b w x 0 x)
  simp only [bank_zero, write_zero] at hc
  have hm := move_work b 0 x 0 x
  simp only [Nat.zero_add] at hm
  have hk : 7*x+w+4 = ((3*x+1)+(2*x+1))+(w+1)+(2*x+1) := by omega
  have hout : bank b x x 0 0 = write b 0 x := by rw [← write_zero b w x 0 0 x, hb]
  have hs := compose (compose (compose ht hr) hc) hm
  dsimp only
  constructor
  · rw [show 7*b 4+b 0+4 = 7*x+w+4 from rfl, hk, hs.1, hout]
  constructor
  · rw [show 7*b 4+b 0+4 = 7*x+w+4 from rfl, hk, hs.2]
  · omega

end Shared.Beeping.NPcoNP.Source284GraphInputCopy
