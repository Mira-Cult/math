import Shared.Beeping.NPcoNP.Grammar284HalfGraphZero
import Shared.Beeping.NPcoNP.Grammar284HalfOddShape

/-! The odd-valued native HALF graph branch updates the selected register to
its quotient and emits no event. Physical execution is separate. -/
namespace Shared.Beeping.NPcoNP.Grammar284HalfOddGraph
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284HalfGraphZero
open Shared.Beeping.NPcoNP.Parent290Coalesced
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem half_odd_step (row : Fin 185) (path : Path) (name : String) (q : Fin 284) (r : Fin 12)
    (leaf : graphLeaf row=some (path,name)) (entry : operationEntry name=some q)
    (reg : expectedRegister q=some r) (bank : Bank 12) (value : Nat)
    (selected : bank r=value) (odd : value%2=1) :
    target.system.step ⟨row,bank⟩=(⟨target.code[row].yes,write bank r (value/2)⟩,[]) := by
  have action := half_action row path name q r leaf entry reg
  have hne : value%2≠0 := by omega
  change ((⟨if ((target.code[row]).action.execute bank).success then target.code[row].yes
      else target.code[row].no, ((target.code[row]).action.execute bank).bank⟩ : Config 12 185),
      ((target.code[row]).action.execute bank).output) = _
  rw [action]
  simp [MaskInvariant.Action.execute,selected,hne]

#print axioms half_odd_step
end Shared.Beeping.NPcoNP.Grammar284HalfOddGraph
