import Shared.PNP.Record285.DispatcherInvariant

/-! Universal ordinary increment for every literal preserving route from
the dispatcher root to the selected physical increment terminal. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DispatcherIncrement
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.DispatcherInvariant

/-- The physical proof covers every literal forward route to the chosen
increment terminal, with exact full tape, progress and event accounting. -/
theorem all_routes_increment_physical (gap target : Nat) (before suffix : List Nat)
    (hindex : before.length < 15) (code : List Bool)
    (hroute : route treeRoot code = some (IncrementPreparation.terminal before.length))
    (head : Int) (leftTail retained : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨IncrementPreparation.terminal before.length,head,
      SymbolicDispatch.bits (SymbolicDispatch.pathLeft code) leftTail,false,
      2*runPattern false gap true
        (2*IncrementSelector.blocksBits (before++[target]) (IncrementShift.suffixBits suffix retained))⟩ physical) :
    let selected := gap::(before++[target])
    let n := (IncrementCleanup.peel (SymbolicDispatch.pathLeft code)).1
    let far := SymbolicDispatch.bits (IncrementCleanup.peel (SymbolicDispatch.pathLeft code)).2 leftTail
    let updated := IncrementSelector.blocksBits (before++[target+1])
      (IncrementSelector.blocksBits suffix retained)
    let steps := ((2*gap+5) + SymbolicDispatch.pathCost code +
      2*(IncrementSelector.cost selected+IncrementShift.cost suffix)) + (3*n+2*gap+9)
    Rel (atLeftWord IncrementPreparation.dispatch0 (head-n-2) far
      (1+2*runPattern false (n+gap+2) true (2*updated)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  have hcheck := all_increment_routes_checked code before.length hindex hroute
  have h := IncrementCleanup.terminal_through_cleanup_physical gap target before suffix hindex
    code hcheck head leftTail retained physical hrel
  exact ⟨h.1,h.2,IncrementCleanup.terminal_cleanup_steps_positive gap target before suffix code⟩

def nextTree : Fin 285 := ⟨192,by decide⟩

theorem root_one : NumericTables.target.table.row treeRoot true = ⟨true,.right,nextTree,false⟩ := by decide

theorem next_one : NumericTables.target.table.row nextTree true =
    ⟨false,.left,IncrementPreparation.break0,false⟩ := by decide

theorem terminal_small (i : Nat) : (IncrementPreparation.terminal i).val < 109 := by
  unfold IncrementPreparation.terminal
  split <;> decide

/-- Every preserving path from the root to an increment terminal contains a
zero, so cleanup cannot carry through the `110` root. -/
theorem route_has_zero (code : List Bool) (i : Nat)
    (hroute : route treeRoot code = some (IncrementPreparation.terminal i)) : false ∈ code := by
  have hs := terminal_small i
  cases code with
  | nil =>
    simp only [route,Option.some.injEq] at hroute
    have hv := congrArg Fin.val hroute
    simp [treeRoot] at hv
    omega
  | cons b bs =>
    cases b with
    | false => simp
    | true =>
      cases bs with
      | nil =>
        simp only [route,root_one] at hroute
        simp only [true_and,if_true,Option.some.injEq] at hroute
        have hv := congrArg Fin.val hroute
        simp [nextTree] at hv
        omega
      | cons b bs =>
        cases b with
        | false => simp
        | true => simp [route,root_one,next_one] at hroute

/-- The complete root and its six-zero margin survive cleanup for every
literal preserving route, not just the original 15 example words. -/
theorem all_routes_preserve_root (code : List Bool) (i : Nat)
    (hroute : route treeRoot code = some (IncrementPreparation.terminal i)) :
    IncrementCleanup.peel (SymbolicDispatch.pathLeft code) =
      ((IncrementCleanup.peel code.reverse).1,
        (IncrementCleanup.peel code.reverse).2 ++ [false,true,true] ++ List.replicate 6 false) :=
  IncrementCleanup.path_peel_preserves_root code (route_has_zero code i hroute)

end Shared.PNP.Record285.DispatcherIncrement
