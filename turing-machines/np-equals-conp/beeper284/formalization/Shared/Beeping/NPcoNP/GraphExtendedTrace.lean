import Shared.Beeping.NPcoNP.GraphExtended284

/-! Operational consequence of a successful literal graph/program check.
No concrete graph is asserted to pass the check here. Each decoded graph
step performs exactly one extended-register step, including HALF, and emits
exactly the same ordered word. -/
namespace Shared.Beeping.NPcoNP.GraphExtendedTrace
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.GraphExtended284
open Shared.Beeping.NPcoNP.MaskInvariant
open PASoundness.RegisterMachine
open PASoundness

abbrev Cfg := Config 12 185

/-- A missing or malformed graph row makes the interpreter fail explicitly. -/
def graphStep (g : Graph) (c : Cfg) : Option (Cfg × List Bool) := do
  let row ← g.rows[c.state.val]?
  let ins ← decode row
  let result := ins.action.execute c.bank
  pure (⟨if result.success then ins.yes else ins.no, result.bank⟩, result.output)

theorem graphStep_eq (g : Graph) (p : MaskInvariant.Program 12 185)
    (h : graphMatches g p = true) (c : Cfg) :
    graphStep g c = some (p.system.step c) := by
  obtain ⟨_, _, hall⟩ := graphMatches_sound g p h
  obtain ⟨row, hr, hd⟩ := hall c.state
  simp [graphStep, hr, hd, MaskInvariant.Program.system]

/-- A finite graph run returns its final configuration and the complete
ordered output word, or fails if any row fails to decode. -/
def graphTrace (g : Graph) (c : Cfg) : Nat → Option (Cfg × List Bool)
  | 0 => some (c, [])
  | n+1 => do
    let (next, word) ← graphTrace g c n
    let (next', event) ← graphStep g next
    pure (next', word ++ event)

theorem graphTrace_eq (g : Graph) (p : MaskInvariant.Program 12 185)
    (h : graphMatches g p = true) (c : Cfg) (n : Nat) :
    graphTrace g c n = some (p.system.advance c n, p.system.wordFrom c n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [graphTrace, ih, graphStep_eq g p h,
      WordEventSystem.advance, WordEventSystem.wordFrom]

end Shared.Beeping.NPcoNP.GraphExtendedTrace
