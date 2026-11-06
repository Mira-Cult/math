import Shared.Beeping.NPcoNP.Grammar284HalfZeroReserved
import Shared.Beeping.NPcoNP.Grammar284HalfPositiveWindow

/-! Every native HALF entry preserves a supplied reserved window, for any
selected value. Reachable initialization and special events remain separate. -/
namespace Shared.Beeping.NPcoNP.Grammar284HalfReserved
open PASoundness PASoundness.RegisterMachine Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeGrammarPreterminalDispatch
open Shared.Beeping.NPcoNP.NativeArrayGraphBank
open Shared.Beeping.NPcoNP.NativeHalfZeroGeneralScan
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284ReservedWindow
open Shared.Beeping.NPcoNP.Parent290Coalesced
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem half_step (row : Fin 185) (path : Path) (name : String) (graph : Bank 12)
    (values rest : List Nat) (value : Nat) (origin separator : Int) (t : Int → Bool)
    (window : ReservedWindow row graph origin separator t)
    (leaf : graphLeaf row=some (path,name)) (entry : operationEntry name=some (entryAt values.length))
    (hlen : values.length≤3) (layout : arrayBank graph=values++value::rest) :
    ∃ steps out, 0<steps ∧ (target.system.step ⟨row,graph⟩).2=[] ∧
      ReservedWindow (target.system.step ⟨row,graph⟩).1.state
        (target.system.step ⟨row,graph⟩).1.bank origin separator out ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  cases value with
  | zero => exact Grammar284HalfZeroReserved.zero_step row path name graph values rest origin separator t window leaf entry hlen layout
  | succ m =>
    exact Grammar284HalfPositiveWindow.positive_step_all row path name graph values rest m origin separator t
      window leaf entry hlen (by simpa using layout)

/-- A native HALF entry determines its bank position; the physical bank split
is obtained from the supplied graph bank without an additional layout premise. -/
theorem half_step_all (row : Fin 185) (graph : Bank 12) (origin separator : Int) (t : Int → Bool)
    (window : ReservedWindow row graph origin separator t)
    (named : ∀ path name, graphLeaf row=some (path,name) →
      ∃ k, k≤3 ∧ operationEntry name=some (entryAt k)) :
    ∃ steps out, 0<steps ∧ (target.system.step ⟨row,graph⟩).2=[] ∧
      ReservedWindow (target.system.step ⟨row,graph⟩).1.state
        (target.system.step ⟨row,graph⟩).1.bank origin separator out ∧
      silentSegment machine (cfg 93 (origin+1) t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨path,name,more,hleaf,room,word,left,gap,right,sep,bank,tail⟩ := window
  have window' : ReservedWindow row graph origin separator t :=
    ⟨path,name,more,hleaf,room,word,left,gap,right,sep,bank,tail⟩
  obtain ⟨k,hk,hentry⟩ := named path name hleaf
  let arr := arrayBank graph
  let values := arr.take k
  have harr : k<arr.length := by simp [arr,arrayBank]; omega
  have hlen : values.length=k := by simp [values,List.length_take_of_le (by omega : k≤arr.length)]
  cases hdrop : arr.drop k with
  | nil =>
    have hdlen := congrArg List.length hdrop
    simp only [List.length_drop,List.length_nil] at hdlen
    omega
  | cons value rest =>
    have layout : arrayBank graph=values++value::rest := by
      have he := List.take_append_drop k arr
      simpa only [values,hdrop,arr] using he.symm
    have entry' : operationEntry name=some (entryAt values.length) := by simpa [hlen] using hentry
    exact half_step row path name graph values rest value origin separator t window' hleaf entry' (by omega) layout

#print axioms half_step
#print axioms half_step_all
end Shared.Beeping.NPcoNP.Grammar284HalfReserved
