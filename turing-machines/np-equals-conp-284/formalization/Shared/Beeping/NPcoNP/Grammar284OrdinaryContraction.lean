import Shared.Beeping.NPcoNP.Grammar284ContractedPhysical
import Shared.Beeping.NPcoNP.Grammar284RawCertificate
import Shared.Beeping.NPcoNP.Grammar284GraphOperation

/-! The first expanded successor of a named ordinary row contracts to the
corresponding graph branch. Physical execution is handled separately. -/
namespace Shared.Beeping.NPcoNP.Grammar284OrdinaryContraction
open PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284.ExpandSteps.ProducerTrace
open Shared.Beeping.NPcoNP.GrammarFullRowsCoverage
open Shared.Beeping.NPcoNP.Grammar284GraphLeaf
open Shared.Beeping.NPcoNP.Grammar284Operational
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.Parent290Coalesced
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 100000000

def namedTagOK (entry : Path × String) : Bool :=
  match namedOperation entry.2 with
  | none => true
  | some (_,true) => operationTag entry.2 == some .other
  | some (_,false) => operationTag entry.2 == some .branch

theorem all_named_tags : traceState557.acc.leaves.toList.all namedTagOK=true := by decide

theorem named_tag (entry : Path × String) (member : entry ∈ traceState557.acc.leaves.toList)
    (n : Fin 12) (inc : Bool) (h : namedOperation entry.2=some (n,inc)) :
    operationTag entry.2=some (if inc then .other else .branch) := by
  have hc := List.all_eq_true.mp all_named_tags entry member
  cases inc <;> simpa [namedTagOK,h] using hc

/-- The first expanded successor selected by an ordinary branch contracts to
its corresponding graph target. -/
theorem successor_contracts (state : Fin 185) (path : Path) (name : String)
    (leaf : graphLeaf state=some (path,name)) (n : Fin 12) (inc : Bool)
    (operation : namedOperation name=some (n,inc)) (skip dst : Nat)
    (hskip : skip=0 ∨ (skip=1 ∧ inc=false))
    (hsucc : successor traceState557.acc.starts path skip=some dst) :
    Grammar284.target producerFullRows producerNumbering.map 3 dst =
      some (if skip=0 then target.code[state].yes.val else target.code[state].no.val) := by
  obtain ⟨k,action,yes,no,hk,hraw,_,hyes,hno⟩ := rawCheck_sound state
  have hl : traceState557.acc.leaves[k]?=some (path,name) := by
    have h := leaf
    simp only [graphLeaf,hk] at h
    exact h
  obtain ⟨bound,hget⟩ := Array.getElem?_eq_some_iff.mp hl
  have hc := allRows k bound
  cases hr : producerFullRows[k]? with
  | none => simp [decodeRaw,hr] at hraw
  | some row =>
    simp only [indexedRowCheck,hl,hr,beq_iff_eq] at hc
    have member := graph_leaf_member state path name leaf
    have tag := named_tag (path,name) member n inc operation
    cases inc with
    | true =>
      have hskip0 : skip=0 := by
        rcases hskip with h | ⟨_,h⟩
        · exact h
        · cases h
      subst skip
      have htag : operationTag name=some .other := by simpa using tag
      have hrow : row=⟨name,[dst]⟩ := by
        simpa [fullRow,htag,hsucc] using hc.symm
      subst row
      have hdecode : decodeRaw k=some (action,yes,no) := hraw
      simp only [decodeRaw,hr] at hdecode
      cases hd : Shared.Beeping.NPcoNP.GraphExtended284.decode ⟨name,[0]⟩ with
      | none => simp [hd] at hdecode
      | some ins =>
        simp [hd] at hdecode
        obtain ⟨_,hyesEq,_⟩ := hdecode
        subst yes
        simpa using hyes
    | false =>
      have htag : operationTag name=some .branch := by simpa using tag
      cases h0 : successor traceState557.acc.starts path 0 with
      | none => simp [fullRow,htag,h0] at hc
      | some first =>
        cases h1 : successor traceState557.acc.starts path 1 with
        | none => simp [fullRow,htag,h0,h1] at hc
        | some second =>
          have hrow : row=⟨name,[first,second]⟩ := by
            simpa [fullRow,htag,h0,h1] using hc.symm
          subst row
          have hdecode : decodeRaw k=some (action,yes,no) := hraw
          simp only [decodeRaw,hr] at hdecode
          cases hd : Shared.Beeping.NPcoNP.GraphExtended284.decode ⟨name,[0,0]⟩ with
          | none => simp [hd] at hdecode
          | some ins =>
            simp [hd] at hdecode
            obtain ⟨_,hyesEq,hnoEq⟩ := hdecode
            subst yes
            subst no
            rcases hskip with h | ⟨h,_⟩
            · subst skip
              rw [h0] at hsucc
              have he : first=dst := Option.some.inj hsucc
              subst first
              simpa using hyes
            · subst skip
              rw [h1] at hsucc
              have he : second=dst := Option.some.inj hsucc
              subst second
              simpa using hno

#print axioms successor_contracts
end Shared.Beeping.NPcoNP.Grammar284OrdinaryContraction
