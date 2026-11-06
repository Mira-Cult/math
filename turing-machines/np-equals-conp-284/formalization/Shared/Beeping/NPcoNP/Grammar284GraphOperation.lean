import Shared.Beeping.NPcoNP.Grammar284GraphLeaf
import Shared.Beeping.NPcoNP.NativeAllBankSelectedValue

/-! Static consistency between each named ordinary graph operation and the
physical producer-bank index. Physical control successor remains separate. -/
namespace Shared.Beeping.NPcoNP.Grammar284GraphOperation
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.Coalescing284Map
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.NativeAllBankSelectedValue
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.MaskInvariant
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 100000000

def graphOperationOK (state : Fin 185) : Bool :=
  match graphLeaf state with
  | none => false
  | some (_,name) =>
    match namedOperation name with
    | none => true
    | some (n,increment) =>
      decide (target.code[state].action =
        if increment then .base (.inc (arrayToSuffix n)) else .base (.decNZ (arrayToSuffix n)))

/-- All named ordinary operations select exactly the suffix register of the
corresponding graph instruction. Half and beep rows are not asserted here. -/
theorem all_graph_operations_checked :
    (List.finRange 185).all graphOperationOK = true := by
  decide

theorem graph_named_operation_action (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (n : Fin 12) (increment : Bool)
    (operation : namedOperation name=some (n,increment)) :
    target.code[state].action =
      if increment then .base (.inc (arrayToSuffix n)) else .base (.decNZ (arrayToSuffix n)) := by
  have h := List.all_eq_true.mp all_graph_operations_checked state (by simp)
  simpa only [graphOperationOK,leaf,operation,decide_eq_true_eq] using h

/-- A named increment has exactly the graph bank effect and silent event
word indicated by its selected physical bank value. -/
theorem graph_increment_step (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (n : Fin 12)
    (operation : namedOperation name=some (n,true))
    (bank : Bank 12) (values rest : List Nat) (value : Nat)
    (hlen : values.length=n.val) (layout : arrayBank bank=values++value::rest) :
    target.system.step ⟨state,bank⟩ =
      (⟨target.code[state].yes,write bank (arrayToSuffix n) (value+1)⟩,[]) := by
  have action := graph_named_operation_action state path name leaf n true operation
  have selected := selected_graph_value bank n values rest value hlen layout
  simp only [ite_true] at action
  change ((⟨if ((target.code[state]).action.execute bank).success then target.code[state].yes
      else target.code[state].no, ((target.code[state]).action.execute bank).bank⟩ : Config 12 185),
      ((target.code[state]).action.execute bank).output) = _
  rw [action]
  simp [MaskInvariant.Action.execute,execute,←selected]

/-- On zero, the named decrement leaves the graph bank unchanged and follows
its no branch without emitting an event. -/
theorem graph_decrement_zero_step (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (n : Fin 12)
    (operation : namedOperation name=some (n,false))
    (bank : Bank 12) (values rest : List Nat)
    (hlen : values.length=n.val) (layout : arrayBank bank=values++0::rest) :
    target.system.step ⟨state,bank⟩ = (⟨target.code[state].no,bank⟩,[]) := by
  have action := graph_named_operation_action state path name leaf n false operation
  have selected := selected_graph_value bank n values rest 0 hlen layout
  simp only [Bool.false_eq_true,ite_false] at action
  change ((⟨if ((target.code[state]).action.execute bank).success then target.code[state].yes
      else target.code[state].no, ((target.code[state]).action.execute bank).bank⟩ : Config 12 185),
      ((target.code[state]).action.execute bank).output) = _
  rw [action]
  simp [MaskInvariant.Action.execute,execute,←selected]

/-- On a positive value, the named decrement decreases the selected graph
register and follows its yes branch without emitting an event. -/
theorem graph_decrement_positive_step (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (n : Fin 12)
    (operation : namedOperation name=some (n,false))
    (bank : Bank 12) (values rest : List Nat) (value : Nat)
    (hlen : values.length=n.val) (layout : arrayBank bank=values++(value+1)::rest) :
    target.system.step ⟨state,bank⟩ =
      (⟨target.code[state].yes,write bank (arrayToSuffix n) value⟩,[]) := by
  have action := graph_named_operation_action state path name leaf n false operation
  have selected := selected_graph_value bank n values rest (value+1) hlen layout
  simp only [Bool.false_eq_true,ite_false] at action
  change ((⟨if ((target.code[state]).action.execute bank).success then target.code[state].yes
      else target.code[state].no, ((target.code[state]).action.execute bank).bank⟩ : Config 12 185),
      ((target.code[state]).action.execute bank).output) = _
  rw [action]
  simp [MaskInvariant.Action.execute,execute,←selected]

#print axioms all_graph_operations_checked
#print axioms graph_named_operation_action
#print axioms graph_increment_step
#print axioms graph_decrement_zero_step
#print axioms graph_decrement_positive_step
end Shared.Beeping.NPcoNP.Grammar284GraphOperation
