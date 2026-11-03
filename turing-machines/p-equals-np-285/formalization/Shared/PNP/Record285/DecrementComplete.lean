import Shared.PNP.Record285.DecrementNonzeroRoot

/-! One full-tape root contract for both ordinary decrement outcomes. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementComplete
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementCleanup (peel)
open Shared.PNP.Record285.IncrementShift (suffixBits)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar

/-- The control prefix after the source's zero/nonzero branch. -/
def resultPrefix (code : List Bool) : Nat → List Bool
  | 0 => (peel (peel code.reverse).2).2.reverse
  | _+1 => (peel code.reverse).2.reverse

def resultControl (code : List Bool) : Nat → Option (List Bool)
  | 0 => returnPathSkipOne code
  | _+1 => returnPath code

/-- Entire numeric tape at the next root. The positive case records the
extra zero field at the finite bank boundary before the retained suffix. -/
def resultConfig (code : List Bool) (gap : Nat) (before fields : List Nat)
    (head : Int) (leftTail retained : Nat) : Nat → PhysicalNumeric.Config 285
  | 0 =>
    let p := peel code.reverse
    let q := peel p.2
    let precode := q.2.reverse
    let bank := IncrementSelector.blocksBits (before++[0]) (suffixBits fields retained)
    denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
      (head-p.1-q.1-2) leftTail (runPattern false (p.1+q.1+gap+2) true (2*bank))
  | k+1 =>
    let p := peel code.reverse
    let precode := p.2.reverse
    let bank := IncrementSelector.blocksBits (before++[k]++fields++[0]) retained
    denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
      (head-p.1-1) leftTail (runPattern false (p.1+gap+1) true (2*bank))

/-- Every ordinary decrement grammar instruction, zero or positive, advances
from the specified clean root to its next root in positive finite time with
no event, exact full tape, and the correct branch-specific control rule. -/
theorem root_decrement_complete (code : List Bool) (gap target : Nat)
    (before fields : List Nat) (hwalk : walk 162 code = some (.dec before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail
      (2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (suffixBits fields retained)))) physical) :
    resultControl code target = some (resultPrefix code target++[true]) ∧
    ∃ steps, 0 < steps ∧
      Rel (resultConfig code gap before fields head leftTail retained target)
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      ∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t := by
  cases target with
  | zero =>
    have h := DecrementZeroRoot.bound_root_zero_returns_root_physical code gap before hwalk
      head leftTail (suffixBits fields retained) physical hrel
    dsimp only at h
    exact ⟨h.2.1,_,h.2.2.2.2,h.2.2.1,h.2.2.2.1⟩
  | succ k =>
    have h := DecrementNonzeroRoot.bound_root_nonzero_returns_root_physical code gap k before fields hwalk
      head leftTail retained physical hrel
    dsimp only at h
    exact ⟨h.2.1,_,h.2.2.2.2,h.2.2.1,h.2.2.2.1⟩

end Shared.PNP.Record285.DecrementComplete
