import Shared.PNP.Record285.GrammarGraphCheck

/-! Clean native-half terminal preparation. The common preparation
machinery is shared with increment; the later half is not assumed. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.HalfPreparation
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.Grammar (halfTerminal)

def selector (i : Nat) : Fin 285 :=
  ⟨(71+i) % 285, Nat.mod_lt _ (by decide)⟩

def terminalCheck (i : Nat) : Bool :=
  decide (NumericTables.target.table.row (halfTerminal i) false =
    ⟨true,.right,IncrementPreparation.prep1,false⟩) &&
  decide (NumericTables.target.table.row (halfTerminal i) true =
    ⟨false,.right,selector i,false⟩)

theorem terminal_check_all : (List.range 4).all terminalCheck = true := by decide

theorem terminal_rows (i : Nat) (hi : i < 4) :
    Record285.machine.table.row (halfTerminal i) false = ⟨true,.right,IncrementPreparation.prep1,false⟩ ∧
    Record285.machine.table.row (halfTerminal i) true = ⟨false,.right,selector i,false⟩ := by
  have h := List.all_eq_true.mp terminal_check_all i (List.mem_range.mpr hi)
  simp only [terminalCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  simpa only [ArtifactEndpoint.literal_rows] using h

theorem literal_rows (i : Nat) (hi : i < 4) :
    IncrementPreparation.Rows Record285.machine (halfTerminal i) := by
  let common := IncrementPreparation.literal_rows 0 (by decide)
  exact ⟨(terminal_rows i hi).1,common.prepOneZero,common.prepTwoZero,
    common.prepTwoOne,common.breakZero,common.breakOne,common.dispatchZero,
    common.dispatchOne,common.dispatch1Zero,common.dispatch1One⟩

/-- Every clean half terminal marks its path and completes preparation in
finite time, preserving the full tape and emitting no event. -/
theorem literal_prepare (i : Nat) (hi : i < 4) (g : Nat) (head : Int) (left tail : Nat) :
    silent Record285.machine (2*g+5)
      ⟨halfTerminal i,head,left,false,2*runPattern false g true tail⟩ =
      some (atLeftWord IncrementPreparation.dispatch0 (head-1) left
        (1+4*pushBit (g+1) true tail)) :=
  IncrementPreparation.prepare_to_dispatch Record285.machine (halfTerminal i)
    (literal_rows i hi) g head left tail

theorem literal_prepare_physical (i : Nat) (hi : i < 4) (g : Nat)
    (head : Int) (left tail : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨halfTerminal i,head,left,false,2*runPattern false g true tail⟩ physical) :
    Rel (atLeftWord IncrementPreparation.dispatch0 (head-1) left
      (1+4*pushBit (g+1) true tail))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run (2*g+5)) ∧
    ∀ t, t < 2*g+5 → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t :=
  silent_physical Record285.machine _ physical hrel _ _ (literal_prepare i hi g head left tail)

end Shared.PNP.Record285.HalfPreparation
