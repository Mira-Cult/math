import Shared.Beeping.NPcoNP.Grammar284ExpansionComplete
import Shared.Beeping.NPcoNP.Grammar284CoreAST

/-! Connect each retained graph row to its originating producer expansion
leaf. This finite lookup does not prove physical control routing. -/
namespace Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284ExpansionComplete
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.GraphCandidate284
open Shared.Beeping.NPcoNP.GraphCandidate284Coverage
open Shared.Beeping.NPcoNP.GraphExtended284
open Shared.Beeping.NPcoNP.Parent290Coalesced
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 100000000

/-- Map a retained graph state to its originating expanded grammar leaf. -/
def graphLeaf (state : Fin 185) : Option (Path × String) := do
  let i ← producerNumbering.kept[state.val]?
  traceState557.acc.leaves[i]?

def graphLeafOK (state : Fin 185) : Bool :=
  match graphLeaf state, graph.rows[state.val]? with
  | some (_,name), some row => name == row.op
  | _, _ => false

/-- All 185 retained graph rows have a corresponding expanded leaf with the
same operation name. -/
theorem all_graph_leaves_checked : (List.finRange 185).all graphLeafOK = true := by
  decide

theorem graph_leaf_checked (state : Fin 185) :
    ∃ path name row, graphLeaf state=some (path,name) ∧
      graph.rows[state.val]?=some row ∧ name=row.op := by
  have h := List.all_eq_true.mp all_graph_leaves_checked state (by simp)
  cases hl : graphLeaf state with
  | none => simp [graphLeafOK,hl] at h
  | some entry =>
    cases hr : graph.rows[state.val]? with
    | none => simp [graphLeafOK,hl,hr] at h
    | some row =>
      rcases entry with ⟨path,name⟩
      simp only [graphLeafOK,hl,hr,beq_iff_eq] at h
      exact ⟨path,name,row,rfl,rfl,h⟩

/-- A successful graph-leaf lookup refers to an actual leaf of the certified
producer expansion. -/
theorem graph_leaf_member (state : Fin 185) (path : Path) (name : String)
    (lookup : graphLeaf state=some (path,name)) :
    (path,name) ∈ traceState557.acc.leaves.toList := by
  change (producerNumbering.kept[state.val]?).bind
    (fun i => traceState557.acc.leaves[i]?) = some (path,name) at lookup
  obtain ⟨i,_,hi⟩ := Option.bind_eq_some_iff.mp lookup
  have hlist : traceState557.acc.leaves.toList[i]?=some (path,name) := by
    simpa only [Array.getElem?_toList] using hi
  obtain ⟨bound,he⟩ := List.getElem?_eq_some_iff.mp hlist
  rw [←he]
  exact List.getElem_mem bound

/-- Every graph row has an actual prepared producer-grammar walk with its
operation name. This is a static control correspondence, not a physical
successor or machine-step simulation. -/
theorem every_graph_row_has_prepared_leaf (state : Fin 185) :
    ∃ path name row, graphLeaf state=some (path,name) ∧
      graph.rows[state.val]?=some row ∧ name=row.op ∧ PreparedWalk path (.op name) := by
  obtain ⟨path,name,row,hleaf,hrow,hname⟩ := graph_leaf_checked state
  have member := graph_leaf_member state path name hleaf
  have walk := (expanded_leaf_iff traceState557.acc producerExpand path name).1 member
  exact ⟨path,name,row,hleaf,hrow,hname,walk⟩

/-- Each graph instruction is decoded from the row associated with its
actual prepared grammar leaf. This relates names and instruction data only;
the physical successor remains a separate obligation. -/
theorem every_target_instruction_has_prepared_leaf (state : Fin 185) :
    ∃ path name row, graphLeaf state=some (path,name) ∧
      graph.rows[state.val]?=some row ∧ name=row.op ∧ PreparedWalk path (.op name) ∧
      decode row=some target.code[state] := by
  obtain ⟨path,name,row,hleaf,hrow,hname,hwalk⟩ := every_graph_row_has_prepared_leaf state
  obtain ⟨row',hrow',hdecode⟩ := rowMatches_sound graph target state (all_rows state)
  rw [hrow] at hrow'
  have he : row=row' := Option.some.inj hrow'
  subst row'
  exact ⟨path,name,row,hleaf,hrow,hname,hwalk,hdecode⟩

#print axioms all_graph_leaves_checked
#print axioms graph_leaf_checked
#print axioms every_graph_row_has_prepared_leaf
#print axioms every_target_instruction_has_prepared_leaf
end Shared.Beeping.NPcoNP.Grammar284GraphLeaf
