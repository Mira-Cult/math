import Shared.Beeping.NPcoNP.Grammar284HalfZeroInfinite
import Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch

/-! Finite graph certificate for the path shape and contracted odd branch
of each native HALF leaf. This does not prove the physical operation. -/
namespace Shared.Beeping.NPcoNP.Grammar284HalfOddShape
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284ExpansionPaths
open Shared.Beeping.NPcoNP.Grammar284Depth
open Shared.Beeping.NPcoNP.Grammar284SuccessorShapeBase
open Shared.Beeping.NPcoNP.Grammar284SuccessorShape
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.Parent290Coalesced
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 200000000

def isHalfEntry (q : Fin 284) : Bool := q=74 ∨ q=75 ∨ q=76 ∨ q=77

def rowCheck (row : Fin 185) : Bool :=
  match graphLeaf row with
  | none => true
  | some (path,name) =>
    match operationEntry name with
    | none => true
    | some q => if isHalfEntry q then
        successorShape path 0 && rightmostOK path 0 && (path.getLast? == some false) &&
        match successor traceState557.acc.starts path 0 with
        | none => false
        | some dst => Grammar284.target producerFullRows producerNumbering.map 3 dst == some target.code[row].yes.val
      else true

theorem all_rows_checked : (List.finRange 185).all rowCheck=true := by decide

theorem half_odd_shapes (row : Fin 185) (path : Path) (name : String) (q : Fin 284)
    (leaf : graphLeaf row=some (path,name)) (entry : operationEntry name=some q)
    (hq : q=74 ∨ q=75 ∨ q=76 ∨ q=77) :
    successorShape path 0=true ∧ rightmostOK path 0=true ∧ path.getLast?=some false ∧
    ∃ dst, successor traceState557.acc.starts path 0=some dst ∧
      Grammar284.target producerFullRows producerNumbering.map 3 dst=some target.code[row].yes.val := by
  have hh := List.all_eq_true.mp all_rows_checked row (List.mem_finRange row)
  have hq' : isHalfEntry q=true := by simpa [isHalfEntry] using hq
  simp only [rowCheck,leaf,entry,hq',Bool.true_eq,if_true,Bool.and_eq_true,beq_iff_eq] at hh
  cases hs : successor traceState557.acc.starts path 0 with
  | none => simp [hs] at hh
  | some dst =>
    simp only [hs,Bool.and_eq_true,beq_iff_eq] at hh
    exact ⟨hh.1.1.1,hh.1.1.2,hh.1.2,dst,rfl,hh.2⟩

#print axioms half_odd_shapes
end Shared.Beeping.NPcoNP.Grammar284HalfOddShape
