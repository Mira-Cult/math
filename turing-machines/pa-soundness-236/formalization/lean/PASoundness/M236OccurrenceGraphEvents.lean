import PASoundness.M236CoherentExecution
/-! Exact output polarity of each retained graph operation on the selected run. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236 PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines

def outputForOp (op : String) : List Bool :=
  if op = "emit.0" then [false] else if op = "emit.1" then [true] else []

theorem effect_output (edge : Grammar.Edge) (op : String)
    (bank bank' : RegisterMachine.Bank 9) (reserve reserve' : List Nat) (events : List Bool)
    (hlabel : GraphLabel edge op) (heffect : BranchEffect edge bank reserve bank' reserve' events) :
    events = outputForOp op := by
  cases heffect with
  | inc r write bank reserve => fin_cases r <;> simp_all [GraphLabel, outputForOp, Selector.registerNames]
  | positive r write bank reserve v h => fin_cases r <;> simp_all [GraphLabel, outputForOp, Selector.registerNames]
  | zero r write bank reserve h => fin_cases r <;> simp_all [GraphLabel, outputForOp, Selector.registerNames]
  | continue1 => simp_all [GraphLabel, outputForOp]
  | continue2 => simp_all [GraphLabel, outputForOp]
  | continue3 => simp_all [GraphLabel, outputForOp]
  | break1 => simp_all [GraphLabel, outputForOp]
  | break3 => simp_all [GraphLabel, outputForOp]
  | emitContinue b => cases b <;> simp_all [GraphLabel, outputForOp, Emit.emitName]
  | emitCleanup b => cases b <;> simp_all [GraphLabel, outputForOp, Emit.emitName]
/-- A projected step emits exactly the bit named by its retained row. -/
theorem witness_step_output (a b : GraphState) (events : List Bool)
    (op : String) (dest : Nat) (extra : Option Nat)
    (hrow : sourceRows[a.index]? = some (op, dest, extra))
    (hstep : WitnessStep a b events) : events = outputForOp op := by
  obtain ⟨edge, op', dest', extra', _, hrow', hlabel, _, heffect⟩ := hstep
  have heq : (op', dest', extra') = (op, dest, extra) := Option.some.inj (hrow'.symm.trans hrow)
  cases heq
  exact effect_output edge _ _ _ _ _ _ hlabel heffect

/-- At every coherent graph boundary, the actual selected blank run appends
exactly the event named by that graph row. -/
theorem selected_segment_output (n : Nat) (op : String) (dest : Nat) (extra : Option Nat)
    (hrow : sourceRows[(states n).val.index]? = some (op, dest, extra)) :
    (machineWordSystem machine machineLabels).prefixWord (89821408 + elapsed (n+1)) =
    (machineWordSystem machine machineLabels).prefixWord (89821408 + elapsed n) ++ outputForOp op := by
  have hs : WitnessStep (states n).val.graphState (segment n).after.graphState (segment n).events :=
    graph_step_projects _ _ _ _ (segment n).valid
  have ho := witness_step_output _ _ _ op dest extra hrow hs
  rw [(selected_coherent_execution.2.2 (n+1)).2.2.2,
      (selected_coherent_execution.2.2 n).2.2.2, output, ho]

example : outputForOp "emit.0" = [false] := by decide
example : outputForOp "emit.1" = [true] := by decide
example : outputForOp "jump" = [] := by decide
example : outputForOp "3.k.a.inc" = [] := by decide

end PASoundness.M236.OccurrenceGraph
