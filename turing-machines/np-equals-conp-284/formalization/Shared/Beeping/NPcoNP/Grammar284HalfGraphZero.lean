import Shared.Beeping.NPcoNP.Grammar284HalfZeroShape

/-! The graph instruction corresponding to each native HALF entry and its
zero-value branch. This finite certificate concerns the graph, not the table. -/
namespace Shared.Beeping.NPcoNP.Grammar284HalfGraphZero
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Parent290Coalesced
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 200000000

def expectedRegister (q : Fin 284) : Option (Fin 12) :=
  match q.val with
  | 74 => some 0
  | 75 => some 1
  | 76 => some 2
  | 77 => some 9
  | _ => none

def rowCheck (row : Fin 185) : Bool :=
  match graphLeaf row with
  | none => true
  | some (_,name) =>
    match operationEntry name with
    | none => true
    | some q => match expectedRegister q with
      | none => true
      | some r => match target.code[row].action with
        | .half r' => r' == r
        | _ => false

theorem all_rows_checked : (List.finRange 185).all rowCheck=true := by decide

theorem half_action (row : Fin 185) (path : Path) (name : String) (q : Fin 284) (r : Fin 12)
    (leaf : graphLeaf row=some (path,name)) (entry : operationEntry name=some q)
    (reg : expectedRegister q=some r) : target.code[row].action=MaskInvariant.Action.half r := by
  have hh := List.all_eq_true.mp all_rows_checked row (List.mem_finRange row)
  simp only [rowCheck,leaf,entry,reg] at hh
  change (match target.code[row].action with | .half r' => r' == r | _ => false) = true at hh
  cases ha : target.code[row].action with
  | base op => rw [ha] at hh; contradiction
  | half r' =>
    simp only [ha,beq_iff_eq] at hh
    simpa only [hh] using ha

theorem half_zero_step (row : Fin 185) (path : Path) (name : String) (q : Fin 284) (r : Fin 12)
    (leaf : graphLeaf row=some (path,name)) (entry : operationEntry name=some q)
    (reg : expectedRegister q=some r) (bank : Bank 12) (zero : bank r=0) :
    target.system.step ⟨row,bank⟩=(⟨target.code[row].no,bank⟩,[]) := by
  have action := half_action row path name q r leaf entry reg
  have hw : write bank r 0=bank := by
    funext i
    by_cases hi : i=r
    · subst i; simp [write,zero]
    · simp [write,hi]
  change ((⟨if ((target.code[row]).action.execute bank).success then target.code[row].yes
      else target.code[row].no, ((target.code[row]).action.execute bank).bank⟩ : Config 12 185),
      ((target.code[row]).action.execute bank).output) = _
  rw [action]
  simp [MaskInvariant.Action.execute,zero,hw]

#print axioms half_zero_step
end Shared.Beeping.NPcoNP.Grammar284HalfGraphZero
