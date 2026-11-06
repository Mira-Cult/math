import Shared.Beeping.NPcoNP.Parent290Coalesced
set_option maxRecDepth 4096

/-! Finite initialization prefix in the checked 284 producer register graph.
At PC 10 the graph clears suffix registers 5 and 6 and initializes register 6
with the parser's sentinel 1. This starts from an arbitrary supplied bank; it
is not a blank-tape reachability or complete parser refinement theorem. -/
namespace Shared.Beeping.NPcoNP.Source284GraphParserInit
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced

abbrev Bank := PASoundness.RegisterMachine.Bank 12
abbrev Cfg := PASoundness.RegisterMachine.Config 12 185
abbrev System := WordEventSystem Cfg Bool

def r5 : Fin 12 := ⟨5, by decide⟩
def r6 : Fin 12 := ⟨6, by decide⟩
def pc10 : Fin 185 := ⟨10, by decide⟩
def pc11 : Fin 185 := ⟨11, by decide⟩
def pc12 : Fin 185 := ⟨12, by decide⟩
def pc13 : Fin 185 := ⟨13, by decide⟩

private theorem write_self (b : Bank) (r : Fin 12) : write b r (b r) = b := by
  funext q
  by_cases h : q = r
  · subst q; simp [write]
  · simp [write, h]

private theorem write_twice (b : Bank) (r : Fin 12) (x y : Nat) :
    write (write b r x) r y = write b r y := by
  funext q
  by_cases h : q = r <;> simp [write, h]

/-- A silent decrement/test self-loop reaches its exit after exactly the
initial counter plus one transitions. -/
theorem clear_loop (M : System) (q exit : Fin 185) (r : Fin 12)
    (hstep : ∀ b : Bank, M.step ⟨q,b⟩ =
      if b r = 0 then (⟨exit,b⟩, [])
      else (⟨q,write b r (b r - 1)⟩, []))
    (b : Bank) :
    M.advance ⟨q,b⟩ (b r + 1) = ⟨exit,write b r 0⟩ ∧
    M.wordFrom ⟨q,b⟩ (b r + 1) = [] := by
  generalize hn : b r = n
  induction n generalizing b with
  | zero =>
    have he : write b r 0 = b := by simpa [hn] using write_self b r
    simp [hn, WordEventSystem.advance, WordEventSystem.wordFrom, hstep, he]
  | succ n ih =>
    let b' := write b r n
    have hb : b' r = n := by simp [b']
    have hs : M.step ⟨q,b⟩ = (⟨q,b'⟩, []) := by
      simpa [hn, b'] using hstep b
    have hi := ih b' hb
    have he : write b' r 0 = write b r 0 := by simp [b', write_twice]
    have ht : n + 1 + 1 = 1 + (n + 1) := by omega
    rw [ht, M.advance_add, M.wordFrom_add]
    have ha : M.advance ⟨q,b⟩ 1 = ⟨q,b'⟩ := by
      simp [WordEventSystem.advance, hs]
    have hw : M.wordFrom ⟨q,b⟩ 1 = [] := by
      simp [WordEventSystem.advance, WordEventSystem.wordFrom, hs]
    rw [ha, hw, List.nil_append]
    simpa only [he] using hi

theorem row10 (b : Bank) : target.system.step ⟨pc10,b⟩ =
    if b r5 = 0 then (⟨pc11,b⟩, [])
    else (⟨pc10,write b r5 (b r5 - 1)⟩, []) := by
  cases h : b (5 : Fin 12) <;>
    simp [target, pc10, pc11, r5, MaskInvariant.Program.system,
      MaskInvariant.Action.execute, execute, h,
      Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
      CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix]

theorem row11 (b : Bank) : target.system.step ⟨pc11,b⟩ =
    if b r6 = 0 then (⟨pc12,b⟩, [])
    else (⟨pc11,write b r6 (b r6 - 1)⟩, []) := by
  cases h : b (6 : Fin 12) <;>
    simp [target, pc11, pc12, r6, MaskInvariant.Program.system,
      MaskInvariant.Action.execute, execute, h,
      Parent290MaskData.program, CoalescingAlgebra.translateInstruction,
      CoalescingAlgebra.translate, Coalescing284Map.logicalToSuffix]

theorem row12 (b : Bank) : target.system.step ⟨pc12,b⟩ =
    (⟨pc13,write b r6 (b r6 + 1)⟩, []) := by
  simp [target, pc12, pc13, r6, MaskInvariant.Program.system,
    MaskInvariant.Action.execute, execute, Parent290MaskData.program,
    CoalescingAlgebra.translateInstruction, CoalescingAlgebra.translate,
    Coalescing284Map.logicalToSuffix]

/-- An arbitrary bank at PC 10 reaches the parser header after a finite,
strictly positive number of silent steps. Register 5 is zero, register 6
is one, and every other register is unchanged. -/
theorem parser_init (b : Bank) :
    let d := b r5 + b r6 + 3
    let out := target.system.advance ⟨pc10,b⟩ d
    0 < d ∧ out.state = pc13 ∧ out.bank r5 = 0 ∧ out.bank r6 = 1 ∧
      (∀ i, i ≠ r5 → i ≠ r6 → out.bank i = b i) ∧
      target.system.wordFrom ⟨pc10,b⟩ d = [] := by
  let b₁ := write b r5 0
  let b₂ := write b₁ r6 0
  have h₁ := clear_loop target.system pc10 pc11 r5 row10 b
  have h₂ := clear_loop target.system pc11 pc12 r6 row11 b₁
  have hr : b₁ r6 = b r6 := by simp [b₁, write, r5, r6]
  have ht : b r5 + b r6 + 3 = (b r5 + 1) + (b₁ r6 + 1) + 1 := by omega
  have ha : target.system.advance ⟨pc10,b⟩ (b r5 + b r6 + 3) =
      ⟨pc13,write b₂ r6 1⟩ := by
    rw [ht, target.system.advance_add, target.system.advance_add, h₁.1, h₂.1]
    simp [WordEventSystem.advance, row12, b₂]
  have hw : target.system.wordFrom ⟨pc10,b⟩ (b r5 + b r6 + 3) = [] := by
    have hab : target.system.advance ⟨pc10,b⟩ ((b r5 + 1) + (b₁ r6 + 1)) =
        ⟨pc12,b₂⟩ := by
      rw [target.system.advance_add, h₁.1, h₂.1]
    rw [ht, target.system.wordFrom_add, target.system.wordFrom_add,
      hab, h₁.1, h₁.2, h₂.2]
    simp [WordEventSystem.wordFrom, WordEventSystem.advance, row12]
  dsimp
  rw [ha]
  refine ⟨by omega, rfl, ?_, ?_, ?_, hw⟩
  · simp [b₂, b₁, write, r5, r6]
  · simp [write]
  · intro i h5 h6
    simp [b₂, b₁, write, h5, h6]

end Shared.Beeping.NPcoNP.Source284GraphParserInit
