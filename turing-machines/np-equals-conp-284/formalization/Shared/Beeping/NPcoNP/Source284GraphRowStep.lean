import Shared.Beeping.NPcoNP.Source284GraphApplyCorrect

/-! The checked graph's lookup and row-application phases implement the
actual numeric source transition from an explicitly prepared PC-60 bank.
Physical tape refinement and preparation of the PC-60 bank remain separate. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphRowStep

open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyRow
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops
open Shared.Beeping.NPcoNP.Source284GraphApplyCorrect
open Shared.Beeping.NPcoNP.Source284Relative

abbrev Bank := PASoundness.RegisterMachine.Bank 12

/-- The seven-register view extends the existing lookup bank without
changing any of the latter's source or scratch registers. -/
theorem regs_eq_bank (b : Bank) (l r s d a w t : Nat) :
    regs b l r s d a w t =
      Source284GraphFirstIteration.bank (write (write b 8 l) 1 r) s d a w t := by
  funext i
  fin_cases i <;> simp [regs,Source284GraphFirstIteration.bank,write]

/-- The lookup acts on arbitrary source halves and leaves them unchanged. -/
theorem lookup (b : Bank) (l r ordinal description clock : Nat) :
    Seg ⟨60,regs b l r ordinal description 0 description clock⟩
      ⟨68,regs b l r (record description ordinal) description 0 0 clock⟩
      (Source284GraphSkip.lookupCost description ordinal) := by
  have h := Source284GraphSkip.lookup_record (write (write b 8 l) 1 r)
    ordinal description clock
  simpa only [Seg,regs_eq_bank] using h

def ordinal (c : Source284Relative.Config) : Nat := c.state-1+c.right%2

def stepCost (description : Nat) (c : Source284Relative.Config) : Nat :=
  Source284GraphSkip.lookupCost description (ordinal c) +
    applyCost (record description (ordinal c)) c.left (c.right/2)

/-- From a paid lookup handoff, the checked graph finishes one source
transition in positive finite time without emitting an event. The initial
right-half numeral has already been halved, and the caller must prove the
corresponding earlier graph segment separately. -/
theorem row_step (b : Bank) (description clock : Nat) (c : Source284Relative.Config)
    (hstate : c.state ≠ 0) :
    0 < stepCost description c ∧
    Seg ⟨60,regs b c.left (c.right/2) (ordinal c) description 0 description clock⟩
      ⟨50,regs b (Source284Relative.step description c).left
        (Source284Relative.step description c).right
        (Source284Relative.step description c).state description 0 0 clock⟩
      (stepCost description c) := by
  let o := ordinal c
  let row := record description o
  have hl := lookup b c.left (c.right/2) o description clock
  have ha := apply b c.left (c.right/2) row description clock
  have hp := (Source284GraphSkip.lookup (write (write b 8 c.left) 1 (c.right/2))
    o description clock).1
  have hap : 0 < applyCost (record description (ordinal c)) c.left (c.right/2) := by
    simpa only [row,o] using ha.1
  refine ⟨by dsimp only [stepCost]; omega, ?_⟩
  have h := cat hl ha.2
  have hleft : leftAfter row c.left (c.right/2) = (Source284Relative.step description c).left := by
    simp only [Source284Relative.step,hstate,if_false,ordinal] at *
    dsimp [leftAfter,row,o,ordinal]
    split <;> rfl
  have hright : rightAfter row c.left (c.right/2) = (Source284Relative.step description c).right := by
    simp only [Source284Relative.step,hstate,if_false,ordinal] at *
    dsimp [rightAfter,row,o,ordinal]
    split <;> rfl
  have hnext : row/4 = (Source284Relative.step description c).state := by
    simp only [Source284Relative.step,hstate,if_false,ordinal] at *
    dsimp [row,o,ordinal]
    split <;> rfl
  simpa only [stepCost,← hleft,← hright,← hnext,o,row] using h

/-- The same ordered silent segment is obtained from the graph parsed from
the embedded producer grammar. -/
theorem embedded_row_step (b : Bank) (description clock : Nat) (c : Source284Relative.Config)
    (hstate : c.state ≠ 0) :
    ((Grammar284ParseSource.parse Grammar284.SourceChars.source.toList).bind
      (fun g => Grammar284.coreGraph g 53)).bind
      (fun g => GraphExtendedTrace.graphTrace g
        ⟨60,regs b c.left (c.right/2) (ordinal c) description 0 description clock⟩
        (stepCost description c)) =
    some (⟨50,regs b (Source284Relative.step description c).left
        (Source284Relative.step description c).right
        (Source284Relative.step description c).state description 0 0 clock⟩,[]) := by
  rw [Grammar284CoreTrace.embeddedGraph_run]
  have h := (row_step b description clock c hstate).2
  rw [h.1,h.2]

end Shared.Beeping.NPcoNP.Source284GraphRowStep
