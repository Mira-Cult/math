import Shared.Beeping.NPcoNP.MaskInvariant
import Shared.Beeping.NPcoNP.Source284ScanSemantics

/-! Local control facts for the marker/payload loop in the coalesced 284
register graph. The row hypotheses isolate the only instructions used by the
proof. These statements do not assert reachability or a tape refinement. -/

namespace Shared.Beeping.NPcoNP.Source284GraphParserLoop

open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.MaskInvariant

abbrev Program := Shared.Beeping.NPcoNP.MaskInvariant.Program 12 185

/-- A silent `DECNZ r0` loop at label 22 followed by label 23. -/
def ClearRow (p : Program) : Prop :=
  p.code[22] = ⟨.base (.decNZ 0), 22, 23⟩

theorem clear_step_zero (p : Program) (row : ClearRow p)
    (b : Bank 12) (h : b 0 = 0) :
    p.system.step ⟨22,b⟩ = (⟨23,b⟩,[]) := by
  simp [Shared.Beeping.NPcoNP.MaskInvariant.Program.system, ClearRow] at row ⊢
  simp [row, Action.execute, PASoundness.RegisterMachine.execute, h]

theorem clear_step_succ (p : Program) (row : ClearRow p)
    (b : Bank 12) (n : Nat) (h : b 0 = n+1) :
    p.system.step ⟨22,b⟩ = (⟨22,write b 0 n⟩,[]) := by
  simp [Shared.Beeping.NPcoNP.MaskInvariant.Program.system, ClearRow] at row ⊢
  simp [row, Action.execute, PASoundness.RegisterMachine.execute, h]

/-- The clearing loop finishes after exactly one test per unit plus the
final unsuccessful test, without output and without changing other registers. -/
theorem clear_segment (p : Program) (row : ClearRow p)
    (n : Nat) (b : Bank 12) (h : b 0 = n) :
    p.system.advance ⟨22,b⟩ (n+1) = ⟨23,write b 0 0⟩ ∧
      p.system.wordFrom ⟨22,b⟩ (n+1) = [] := by
  induction n generalizing b with
  | zero =>
    have hb : write b 0 0 = b := by
      funext q
      by_cases hq : q = 0 <;> simp [write, hq, h]
    have hs := clear_step_zero p row b h
    constructor
    · simpa [WordEventSystem.advance, hb] using congrArg Prod.fst hs
    · simpa [WordEventSystem.wordFrom, WordEventSystem.advance] using congrArg Prod.snd hs
  | succ n ih =>
    have hs := clear_step_succ p row b n h
    have ha : p.system.advance ⟨22,b⟩ 1 = ⟨22,write b 0 n⟩ := by
      simpa [WordEventSystem.advance] using congrArg Prod.fst hs
    have hw : p.system.wordFrom ⟨22,b⟩ 1 = [] := by
      simpa [WordEventSystem.wordFrom, WordEventSystem.advance] using congrArg Prod.snd hs
    have ht := ih (write b 0 n) (by simp)
    have hh : write (write b 0 n) 0 0 = write b 0 0 := by
      funext q
      by_cases hq : q = 0 <;> simp [write, hq]
    have hn : n+1+1 = 1+(n+1) := by omega
    rw [hn, WordEventSystem.advance_add, WordEventSystem.wordFrom_add, ha, hw]
    simpa [hh] using ht

/-- HALF dispatch rows for the marker and its payload. -/
def MarkerRows (p : Program) : Prop :=
  p.code[13] = ⟨.half 0, 14, 22⟩ ∧
  p.code[19] = ⟨.half 0, 20, 21⟩ ∧
  p.code[20] = ⟨.base (.inc 6), 21, 21⟩ ∧
  p.code[21] = ⟨.base (.inc 5), 13, 13⟩

/-- The marker is consumed in one silent step and dispatches by its low bit. -/
theorem marker_step (p : Program) (rows : MarkerRows p) (b : Bank 12) :
    p.system.step ⟨13,b⟩ =
      (⟨if b 0 % 2 = 0 then 22 else 14, write b 0 (b 0 / 2)⟩,[]) := by
  rcases rows with ⟨h13, _, _, _⟩
  have hb : b 0 % 2 = 0 ∨ b 0 % 2 = 1 := by omega
  rcases hb with h | h <;>
    simp [Shared.Beeping.NPcoNP.MaskInvariant.Program.system, h13,
      Action.execute, h]

/-- The second HALF reads the payload. Subsequent rows increment the
description accumulator only on the odd branch and increment the length on
both branches. -/
theorem payload_steps (p : Program) (rows : MarkerRows p) (b : Bank 12) :
    let bit := b 0 % 2
    let k := if bit = 0 then 2 else 3
    let result := write (write (write b 0 (b 0 / 2)) 6 (b 6 + bit)) 5 (b 5 + 1)
    p.system.advance ⟨19,b⟩ k = ⟨13,result⟩ ∧
      p.system.wordFrom ⟨19,b⟩ k = [] := by
  rcases rows with ⟨_, h19, h20, h21⟩
  have bit : b 0 % 2 = 0 ∨ b 0 % 2 = 1 := by omega
  rcases bit with h | h <;>
    simp [WordEventSystem.advance, WordEventSystem.wordFrom,
      Shared.Beeping.NPcoNP.MaskInvariant.Program.system, h19, h20, h21,
      Action.execute, PASoundness.RegisterMachine.execute, write, h, funext_iff]
  intro x
  by_cases hx : x = 6 <;> simp_all

end Shared.Beeping.NPcoNP.Source284GraphParserLoop
