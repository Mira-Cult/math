import Shared.Beeping.NPcoNP.Grammar284ContractCoverage
/-! Finite, silent administrative-jump progress for the checked producer.
This does not implement a retained action or prove physical-table refinement. -/

namespace Shared.Beeping.NPcoNP.Grammar284JumpProgress

open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284ContractCoverage
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 16000000

inductive JumpTrace (rows : Array Row) : Nat → Nat → Nat → Prop
  | done (i : Nat) : JumpTrace rows i i 0
  | jump (i j k n : Nat) (row : Row) :
      rows[i]?=some row → row.op="jump" → row.targets=[j] →
      JumpTrace rows j k n → JumpTrace rows i k (n+1)

theorem target_sound (rows : Array Row) (mapping : Array (Option Nat))
    (fuel i result : Nat) (h : target rows mapping fuel i=some result) :
    ∃ final n row, n<fuel ∧ JumpTrace rows i final n ∧ rows[final]?=some row ∧
      row.op≠"jump" ∧ mapping[final]?=some (some result) := by
  induction fuel generalizing i with
  | zero => simp [target] at h
  | succ fuel ih =>
    cases hr : rows[i]? with
    | none => simp [target,hr] at h
    | some row =>
      by_cases hj : row.op="jump"
      · cases ht : row.targets with
        | nil => simp [target,hr,hj,ht] at h
        | cons j js =>
          cases js with
          | nil =>
            have hnext : target rows mapping fuel j=some result := by simpa [target,hr,hj,ht] using h
            obtain ⟨final,n,r,hn,htrace,hfinal,hnot,hmap⟩ := ih j hnext
            exact ⟨final,n+1,r,by omega,JumpTrace.jump i j final n row hr hj ht htrace,hfinal,hnot,hmap⟩
          | cons x xs => simp [target,hr,hj,ht] at h
      · have hm : (mapping[i]?).join=some result := by simpa [target,hr,hj] using h
        cases hmap : mapping[i]? with
        | none => simp [hmap] at hm
        | some value =>
          cases value with
          | none => simp [hmap] at hm
          | some j =>
            have he : j=result := by simpa [hmap] using hm
            subst j
            exact ⟨i,0,row,by omega,JumpTrace.done i,hr,hj,hmap⟩

#print axioms target_sound

/-- Every checked input row reaches a retained row by finitely many jumps. -/
theorem producer_jump_progress (i : Nat) (hi : i<producerFullRows.size) :
    ∃ final n result row, n≤279 ∧ JumpTrace producerFullRows i final n ∧
      producerFullRows[final]?=some row ∧ row.op≠"jump" ∧
      producerNumbering.map[final]?=some (some result) := by
  have hc := allTargets i hi
  unfold targetCheck at hc
  cases ht : target producerFullRows producerNumbering.map (producerFullRows.size+1) i with
  | none => simp [ht] at hc
  | some result =>
    obtain ⟨final,n,row,hn,htrace,hrow,hnot,hmap⟩ := target_sound _ _ _ _ _ ht
    have hsize := fullRows_size
    refine ⟨final,n,result,row,by omega,htrace,hrow,hnot,hmap⟩

/-- A finite chain followed by a chain has the sum of their lengths. -/
theorem jumpTrace_append (rows : Array Row) {i j k n m : Nat}
    (a : JumpTrace rows i j n) (b : JumpTrace rows j k m) : JumpTrace rows i k (n+m) := by
  induction a with
  | done => simpa using b
  | jump i x j n row hrow hjump htargets trace ih =>
    have h := JumpTrace.jump i x k (n+m) row hrow hjump htargets (ih b)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- No jump trace can be longer than a trace that reaches a non-jump row. -/
theorem jumpTrace_le_terminal (rows : Array Row) {i final n : Nat}
    (terminal : JumpTrace rows i final n) (row : Row)
    (hfinal : rows[final]?=some row) (hnot : row.op≠"jump") :
    ∀ {dest k}, JumpTrace rows i dest k → k≤n := by
  induction terminal with
  | done i =>
    intro dest k h
    cases h with
    | done => omega
    | jump i j dest k r hr hj ht tail =>
      rw [hfinal] at hr
      cases hr
      contradiction
  | jump i j final n r hr hj ht tail ih =>
    intro dest k h
    cases h with
    | done => omega
    | jump i j' dest k r' hr' hj' ht' tail' =>
      rw [hr] at hr'
      cases hr'
      rw [ht] at ht'
      have heq : j=j' := by simpa using ht'
      subst j'
      have hh := ih hfinal tail'
      omega

/-- Every administrative chain starting at a producer row has length at
most 279, including chains from rows unreachable from the program entry. -/
theorem producer_jump_bound (i : Nat) (hi : i<producerFullRows.size)
    (dest n : Nat) (h : JumpTrace producerFullRows i dest n) : n≤279 := by
  obtain ⟨final,k,result,row,hk,ht,hrow,hnot,hmap⟩ := producer_jump_progress i hi
  have hb := jumpTrace_le_terminal producerFullRows ht row hrow hnot h
  omega

def JumpEdge (rows : Array Row) (i j : Nat) : Prop :=
  ∃ row, rows[i]?=some row ∧ row.op="jump" ∧ row.targets=[j]

theorem edge_trace (rows : Array Row) {i j : Nat} (h : JumpEdge rows i j) :
    JumpTrace rows i j 1 := by
  obtain ⟨row,hr,hj,ht⟩ := h
  exact JumpTrace.jump i j j 0 row hr hj ht (JumpTrace.done j)

theorem infinite_prefix (rows : Array Row) (f : Nat → Nat)
    (h : ∀ n, JumpEdge rows (f n) (f (n+1))) :
    ∀ n, JumpTrace rows (f 0) (f n) n := by
  intro n
  induction n with
  | zero => exact JumpTrace.done _
  | succ n ih =>
    have ht := edge_trace rows (h n)
    simpa [Nat.add_comm] using jumpTrace_append rows ih ht

/-- The checked producer has no infinite administrative-only run from any
input row, whether or not that row is reached by the source program. -/
theorem producer_no_infinite_jumps (f : Nat → Nat)
    (hstart : f 0<producerFullRows.size)
    (hstep : ∀ n, JumpEdge producerFullRows (f n) (f (n+1))) : False := by
  have h := infinite_prefix producerFullRows f hstep 280
  have hb := producer_jump_bound (f 0) hstart (f 280) 280 h
  omega

#print axioms producer_jump_progress
#print axioms producer_jump_bound
#print axioms producer_no_infinite_jumps

def shortTargetCheck (i : Nat) : Bool :=
  (target producerFullRows producerNumbering.map 3 i).isSome

set_option maxRecDepth 131072 in
set_option maxHeartbeats 30000000 in
theorem allShortTargets : (List.range producerFullRows.size).all shortTargetCheck = true := by decide

theorem producer_short_progress (i : Nat) (hi : i<producerFullRows.size) :
    ∃ final n result row, n≤2 ∧ JumpTrace producerFullRows i final n ∧
      producerFullRows[final]?=some row ∧ row.op≠"jump" ∧
      producerNumbering.map[final]?=some (some result) := by
  have hc := List.all_eq_true.mp allShortTargets i (List.mem_range.mpr hi)
  unfold shortTargetCheck at hc
  cases ht : target producerFullRows producerNumbering.map 3 i with
  | none => simp [ht] at hc
  | some result =>
    obtain ⟨final,n,row,hn,htrace,hrow,hnot,hmap⟩ := target_sound _ _ _ _ _ ht
    exact ⟨final,n,result,row,by omega,htrace,hrow,hnot,hmap⟩

theorem producer_jump_bound_two (i : Nat) (hi : i<producerFullRows.size)
    (dest n : Nat) (h : JumpTrace producerFullRows i dest n) : n≤2 := by
  obtain ⟨final,k,result,row,hk,ht,hrow,hnot,hmap⟩ := producer_short_progress i hi
  have hb := jumpTrace_le_terminal producerFullRows ht row hrow hnot h
  omega

#print axioms allShortTargets
#print axioms producer_jump_bound_two

/-- Two jumps are really needed from full-row 128. -/
theorem producer_two_jump_witness : JumpTrace producerFullRows 128 46 2 := by
  refine JumpTrace.jump 128 133 46 1 ⟨"jump",[133]⟩ (by decide) rfl rfl ?_
  exact JumpTrace.jump 133 46 46 0 ⟨"jump",[46]⟩ (by decide) rfl rfl (JumpTrace.done 46)

/-- Partial administrative evaluator; non-jumps and malformed rows are
rejected. The auxiliary store is arbitrary and cannot be changed by a jump. -/
def jumpStep {α : Type} (rows : Array Row) (c : Nat × α) : Option ((Nat × α) × List Bool) := do
  let row ← rows[c.1]?
  if row.op = "jump" then
    match row.targets with
    | [j] => some ((j,c.2),[])
    | _ => none
  else none

def jumpRun {α : Type} (rows : Array Row) : Nat → (Nat × α) → Option ((Nat × α) × List Bool)
  | 0,c => some (c,[])
  | n+1,c => do
    let (d,w) ← jumpStep rows c
    let (e,v) ← jumpRun rows n d
    pure (e,w++v)

theorem jumpTrace_run {α : Type} (rows : Array Row) {i final n : Nat}
    (h : JumpTrace rows i final n) (store : α) :
    jumpRun rows n (i,store) = some ((final,store),[]) := by
  induction h with
  | done => rfl
  | jump i j k n row hr hj ht tail ih =>
    simp [jumpRun,jumpStep,hr,hj,ht,ih]

/-- Any checked row reaches its contracted destination after at most two
executable silent jumps, preserving every component of the supplied store. -/
theorem producer_jump_execute {α : Type} (i : Nat) (hi : i<producerFullRows.size)
    (store : α) :
    ∃ final n result row, n≤2 ∧
      jumpRun producerFullRows n (i,store) = some ((final,store),[]) ∧
      producerFullRows[final]?=some row ∧ row.op≠"jump" ∧
      producerNumbering.map[final]?=some (some result) := by
  obtain ⟨final,n,result,row,hn,ht,hrow,hnot,hmap⟩ := producer_short_progress i hi
  exact ⟨final,n,result,row,hn,jumpTrace_run _ ht store,hrow,hnot,hmap⟩

#print axioms producer_two_jump_witness
#print axioms producer_jump_execute

/-- Execute one retained action, then its explicit administrative chase.
The action is supplied by the caller; this does not implement it physically. -/
def actionThenJumps {α : Type} (rows : Array Row)
    (action : α → Option ((Nat × α) × List Bool)) (n : Nat) (store : α) :
    Option ((Nat × α) × List Bool) := do
  let (c,w) ← action store
  let (d,v) ← jumpRun rows n c
  pure (d,w++v)

/-- One successful action plus its checked producer jump chase takes one to
three abstract steps and retains exactly the action's event word and store. -/
theorem producer_action_then_jumps {α : Type}
    (action : α → Option ((Nat × α) × List Bool)) (store store' : α)
    (next : Nat) (word : List Bool)
    (hact : action store=some ((next,store'),word)) (hnext : next<producerFullRows.size) :
    ∃ final n result row, 0<n+1 ∧ n+1≤3 ∧
      actionThenJumps producerFullRows action n store = some ((final,store'),word) ∧
      producerFullRows[final]?=some row ∧ row.op≠"jump" ∧
      producerNumbering.map[final]?=some (some result) := by
  obtain ⟨final,n,result,row,hn,hrun,hrow,hnot,hmap⟩ := producer_jump_execute next hnext store'
  refine ⟨final,n,result,row,by omega,by omega,?_,hrow,hnot,hmap⟩
  simp [actionThenJumps,hact,hrun]

#print axioms producer_action_then_jumps

end Shared.Beeping.NPcoNP.Grammar284JumpProgress
