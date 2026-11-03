import Shared.PNP.Record285.OwnershipMapping
import Shared.PNP.Record285.OwnershipCertificate

/-! Quantitative and value-level facts for the ownership-to-class adapter. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.OwnershipCore
open Shared.Beeping
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarExact
open Shared.PNP.Record285.GrammarCoreGraph
open Shared.PNP.Record285.GrammarCoreZero

def WellFormed : Action → Prop
  | .inc i | .dec i | .half i => i < 18
  | .move src dst => src < 18 ∧ dst < 18 ∧ src ≠ dst
  | .beep => True

theorem transfer_wellFormed (row : Row) (before no yes : Array Nat)
    (h : transfer row before no yes = true) : WellFormed row.action := by
  cases row with
  | mk action noidx yesidx =>
    cases action with
    | inc i =>
      simp only [transfer,Bool.and_eq_true_iff,decide_eq_true_eq] at h
      exact h.1.1
    | dec i =>
      simp only [transfer,Bool.and_eq_true_iff,decide_eq_true_eq] at h
      exact h.1.1
    | half i =>
      simp only [transfer,Bool.and_eq_true_iff,decide_eq_true_eq] at h
      exact h.1.1
    | move src dst =>
      simp only [transfer,moveTransfer,Bool.and_eq_true_iff,decide_eq_true_eq] at h
      exact h.1.1.1
    | beep => trivial

theorem valid_row_wellFormed (rows : Array Row) (masks : Array (Array Nat))
    (hcheck : invariantCheck rows masks = true) (s : State) (hvalid : Valid rows masks s)
    (row : Row) (hrow : rows[s.index]? = some row) : WellFormed row.action := by
  obtain ⟨hi,mask,hm,_⟩ := hvalid
  have hrows := (invariant_parts rows masks hcheck).2.2
  have hr := List.all_eq_true.mp hrows s.index (List.mem_range.mpr hi)
  obtain ⟨no,yes,_,_,ht⟩ := invariantRow_sound rows masks s.index row mask hrow hm hr
  exact transfer_wellFormed row mask no yes ht

theorem logical_run_valid (n : Nat) : Valid logicalRows logicalMasks ((system logicalRows).run n) :=
  run_valid logicalRows logicalMasks invariant_checked (by decide) n

theorem mapping_parts (logical : Array Row) (physical : Array CoreRow) (masks : Array (Array Nat))
    (classes mapping : Array Nat) (h : mappingCheck logical physical masks classes mapping = true) :
    logical.size = mapping.size ∧ classes.size = 18 ∧ mapping[0]? = some 0 ∧
      (∀ i, i < 18 → classAt classes i < 15) ∧
      ∀ i, i < logical.size → mappingRow logical physical masks classes mapping i = true := by
  simp only [mappingCheck,Bool.and_eq_true_iff,decide_eq_true_eq] at h
  refine ⟨h.1.1.1,h.1.1.2.1,h.1.1.2.2,?_,?_⟩
  · intro i hi
    have hc := List.all_eq_true.mp h.1.2 i (List.mem_range.mpr hi)
    exact of_decide_eq_true hc
  · intro i hi
    exact List.all_eq_true.mp h.2 i (List.mem_range.mpr hi)

theorem single_index (action : Action) (e : Edge) (i : Nat)
    (he : singleEdge action = some e) (hi : operationIndex e = some i) (classes : Array Nat) :
    operationIndex (targetEdge classes action) = some (classAt classes i) := by
  cases action <;> simp only [singleEdge,Option.some.injEq] at he
  all_goals try contradiction
  all_goals subst e
  all_goals simp_all [operationIndex,targetEdge]

theorem single_value (action : Action) (e : Edge) (i : Nat)
    (he : singleEdge action = some e) (hi : operationIndex e = some i) (classes : Array Nat) (n : Nat) :
    operationValue (targetEdge classes action) n = operationValue e n := by
  cases action <;> simp only [singleEdge,Option.some.injEq] at he
  all_goals try contradiction
  all_goals subst e
  all_goals simp_all [operationIndex,targetEdge,operationValue]

theorem single_branch (action : Action) (e : Edge) (i : Nat)
    (he : singleEdge action = some e) (hi : operationIndex e = some i) (classes : Array Nat) (n : Nat) :
    operationBranch (targetEdge classes action) n = operationBranch e n := by
  cases action <;> simp only [singleEdge,Option.some.injEq] at he
  all_goals try contradiction
  all_goals subst e
  all_goals simp_all [operationIndex,targetEdge,operationBranch]

theorem single_observe (action : Action) (e : Edge) (i : Nat)
    (he : singleEdge action = some e) (hi : operationIndex e = some i) (bank : Nat → Nat) :
    observe action bank = operationBranch e (bank i) := by
  cases action <;> simp only [singleEdge,Option.some.injEq] at he
  all_goals try contradiction
  all_goals subst e
  all_goals simp_all [operationIndex,observe,operationBranch]

theorem single_class_update (action : Action) (e : Edge) (i : Nat)
    (he : singleEdge action = some e) (hindex : operationIndex e = some i)
    (classes : Array Nat) (bank : Nat → Nat) (hi : i < 18) (hiso : Isolated classes bank i) (c : Nat) :
    classSum classes (update action bank) c =
      if c = classAt classes i then operationValue e (bank i) else classSum classes bank c := by
  cases action with
  | inc k =>
    simp only [singleEdge,Option.some.injEq] at he
    subst e
    simp only [operationIndex,Option.some.injEq] at hindex
    subst k
    change classSum classes (fun j => if j = i then bank i + 1 else bank j) c = _
    exact classSum_replace classes bank i (bank i+1) c hi hiso
  | dec k =>
    simp only [singleEdge,Option.some.injEq] at he
    subst e
    simp only [operationIndex,Option.some.injEq] at hindex
    subst k
    change classSum classes (fun j => if j = i then bank i - 1 else bank j) c = _
    exact classSum_replace classes bank i (bank i-1) c hi hiso
  | half k =>
    simp only [singleEdge,Option.some.injEq] at he
    subst e
    simp only [operationIndex,Option.some.injEq] at hindex
    subst k
    change classSum classes (fun j => if j = i then bank i / 2 else bank j) c = _
    exact classSum_replace classes bank i (bank i/2) c hi hiso
  | move src dst => simp [singleEdge] at he
  | beep => simp [singleEdge] at he

def BankRel (classes : Array Nat) (bank : Nat → Nat) (fields : List Nat) : Prop :=
  15 ≤ fields.length ∧ ∀ c, c < 15 → fields.getD c 0 = classSum classes bank c

theorem initial_bankRel (classes : Array Nat) : BankRel classes (fun _ => 0) (List.replicate 1909 0) := by
  refine ⟨by simp,?_⟩
  intro c hc
  rw [zero_classSum]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_replicate]
  split <;> rfl

theorem single_bankRel (classes : Array Nat) (bank : Nat → Nat) (fields : List Nat)
    (action : Action) (e : Edge) (i : Nat) (he : singleEdge action = some e)
    (hindex : operationIndex e = some i) (hi : i < 18) (hc : classAt classes i < 15)
    (hiso : Isolated classes bank i) (hrel : BankRel classes bank fields) :
    BankRel classes (update action bank) (applyUpdate (targetEdge classes action) fields) := by
  have htarget := single_index action e i he hindex classes
  have hlen := hrel.1
  have hoperand : ∀ j, operationIndex (targetEdge classes action) = some j → j < fields.length := by
    intro j hj
    rw [htarget] at hj
    have hj' : classAt classes i = j := Option.some.inj hj
    omega
  have hlength := bank_length_nondecreasing (targetEdge classes action) fields hoperand
  refine ⟨by omega,?_⟩
  intro c hc'
  have hr := bank_update_correct (targetEdge classes action) fields hoperand c (by omega)
  rw [hr,single_class_update action e i he hindex classes bank hi hiso c]
  simp only [updateBank,htarget]
  by_cases hci : c = classAt classes i
  · simp only [hci,if_true]
    have hv : fields.getD (classAt classes i) 0 = bank i := by
      rw [hrel.2 _ hc,isolated_sum classes bank i hi hiso]
    rw [hv,single_value action e i he hindex classes]
  · simp only [hci,if_false]
    exact hrel.2 c hc'

theorem single_test_matches (classes : Array Nat) (bank : Nat → Nat) (fields : List Nat)
    (action : Action) (e : Edge) (i : Nat) (he : singleEdge action = some e)
    (hindex : operationIndex e = some i) (hi : i < 18) (hc : classAt classes i < 15)
    (hiso : Isolated classes bank i) (hrel : BankRel classes bank fields) :
    GrammarControlGraph.test (targetEdge classes action) fields = observe action bank := by
  have htarget := single_index action e i he hindex classes
  rw [graph_test_matches]
  simp only [operandValue,htarget]
  have hv : fields.getD (classAt classes i) 0 = bank i := by
    rw [hrel.2 _ hc,isolated_sum classes bank i hi hiso]
  rw [hv,single_branch action e i he hindex classes,single_observe action e i he hindex bank]

/-- A logical ownership move is implemented by a finite silent loop whose
result continues to represent all fifteen physical classes. -/
theorem move_progress (rows : Array CoreRow) (classes : Array Nat) (bank : Nat → Nat) (fields : List Nat)
    (head body exit src dst : Nat) (hs : src < 18) (hd : dst < 18)
    (hcs : classAt classes src < 15) (hcd : classAt classes dst < 15)
    (hclasses : classAt classes src ≠ classAt classes dst)
    (hsrc : Isolated classes bank src) (hdst : Isolated classes bank dst)
    (hrel : BankRel classes bank fields)
    (hhead : rows[head]? = some ⟨.dec (classAt classes src),body,exit⟩)
    (hbody : rows[body]? = some ⟨.inc (classAt classes dst),head,head⟩) :
    ∃ out, (coreSystem rows).advance ⟨head,fields⟩ (2*bank src+1) = ⟨exit,out⟩ ∧
      BankRel classes (update (.move src dst) bank) out ∧
      ∀ t, t < 2*bank src+1 → ¬ (coreSystem rows).BeepFrom ⟨head,fields⟩ t := by
  have hsrcVal : fields.getD (classAt classes src) 0 = bank src := by
    rw [hrel.2 _ hcs,isolated_sum classes bank src hs hsrc]
  have hdstVal : fields.getD (classAt classes dst) 0 = bank dst := by
    rw [hrel.2 _ hcd,isolated_sum classes bank dst hd hdst]
  obtain ⟨hrun,hlen,hreads,hquiet⟩ := move_loop rows head body exit
    (classAt classes src) (classAt classes dst) (bank src) fields
    hhead hbody hrel.1 hcs hcd hclasses hsrcVal
  refine ⟨_,hrun,⟨hlen,?_⟩,hquiet⟩
  intro c hc
  have hread := hreads c hc
  have hsum := classSum_move classes bank src dst c hs hd hclasses hsrc hdst
  rw [hsum]
  by_cases hsc : c = classAt classes src
  · simp only [hsc,if_true] at hread ⊢
    exact hread
  · by_cases hdc : c = classAt classes dst
    · simp only [hdc,if_true] at hread ⊢
      rw [hdstVal] at hread
      simpa only [Nat.add_comm] using hread
    · simp only [hsc,hdc,if_false] at hread ⊢
      rw [hrel.2 c hc] at hread
      exact hread

end Shared.PNP.Record285.OwnershipCore
