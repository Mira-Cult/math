import Shared.Codes.TM2Statements

/-! Checked execution of one numeric TM2 statement block. This module proves
soundness of successful executions; it does not prove validity, completeness,
recursion-theoretic computability, or a bit-cost bound. -/
namespace Shared.Codes.TM2StatementExecution
open Shared.Codes.TM2Statements
open Shared.Codes.FiniteTables
open Turing.TM2

abbrev Stacks := List (List Nat)
structure Result where
  label : Option Nat
  state : Nat
  memory : Stacks
  deriving DecidableEq, Repr

def symbolIndex : Option Nat → Nat
  | none => 0
  | some x => x + 1

def boolOfNat : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

/-- All runtime state and stacks are finite lists. Invalid stack/table indices
and non-Boolean branch entries return `none`. -/
def exec : Code → Nat → Stacks → Option Result
  | .halt, v, s => some ⟨none, v, s⟩
  | .goto t, v, s => do
      let l ← lookup t v
      return ⟨some l, v, s⟩
  | .push k t q, v, s => do
      let stk ← s[k]?
      let x ← lookup t v
      exec q v (s.set k (x :: stk))
  | .peek k t q, v, s => do
      let stk ← s[k]?
      let v' ← lookup₂ t v (symbolIndex stk.head?)
      exec q v' s
  | .pop k t q, v, s => do
      let stk ← s[k]?
      let v' ← lookup₂ t v (symbolIndex stk.head?)
      exec q v' (s.set k stk.tail)
  | .load t q, v, s => do
      let v' ← lookup t v
      exec q v' s
  | .branch t yes no, v, s => do
      let x ← lookup t v
      let b ← boolOfNat x
      if b then exec yes v s else exec no v s

/-- The mathematical interpretation is used only for the correspondence
proof. Defaulted lookups are irrelevant on successful checked paths. -/
def interpret : Code → Stmt (fun _ : Nat => Nat) Nat Nat
  | .halt => .halt
  | .goto t => .goto fun v => (lookup t v).getD 0
  | .push k t q => .push k (fun v => (lookup t v).getD 0) (interpret q)
  | .peek k t q => .peek k (fun v x => (lookup₂ t v (symbolIndex x)).getD 0) (interpret q)
  | .pop k t q => .pop k (fun v x => (lookup₂ t v (symbolIndex x)).getD 0) (interpret q)
  | .load t q => .load (fun v => (lookup t v).getD 0) (interpret q)
  | .branch t a b => .branch (fun v => (lookup t v).getD 0 == 1) (interpret a) (interpret b)

def stackFn (s : Stacks) (k : Nat) : List Nat := (s[k]?).getD []
def erase (r : Result) : Cfg (fun _ : Nat => Nat) Nat Nat :=
  ⟨r.label, r.state, stackFn r.memory⟩

theorem stackFn_set (s : Stacks) (k : Nat) (x : List Nat) (h : k < s.length) :
    stackFn (s.set k x) = Function.update (stackFn s) k x := by
  funext j
  by_cases hj : j = k
  · subst j
    simp [stackFn, List.getElem?_set_self h]
  · simp [stackFn, List.getElem?_set_ne (Ne.symm hj), Function.update_of_ne hj]

/-- Successful checked execution agrees exactly with the library's complete
statement-block semantics after embedding finite stacks. -/
theorem exec_sound (q : Code) (v : Nat) (s : Stacks) (r : Result)
    (h : exec q v s = some r) :
    stepAux (interpret q) v (stackFn s) = erase r := by
  induction q generalizing v s with
  | halt =>
    simp [exec] at h
    subst r
    rfl
  | goto t =>
    cases ht : lookup t v with
    | none => simp [exec, ht] at h
    | some x =>
      simp [exec, ht] at h
      subst r
      simp [interpret, stepAux, ht, erase]
  | push k t q ih =>
    cases hs : s[k]? with
    | none => simp [exec, hs] at h
    | some stk =>
      cases ht : lookup t v with
      | none => simp [exec, hs, ht] at h
      | some x =>
        have hk : k < s.length := (List.getElem?_eq_some_iff.mp hs).1
        have hh : exec q v (s.set k (x :: stk)) = some r := by simpa [exec, hs, ht] using h
        have hi := ih v (s.set k (x :: stk)) hh
        simp [interpret, stepAux, ht, stackFn, hs, ← stackFn_set s k (x :: stk) hk] at *
        exact hi
  | peek k t q ih =>
    cases hs : s[k]? with
    | none => simp [exec, hs] at h
    | some stk =>
      cases ht : lookup₂ t v (symbolIndex stk.head?) with
      | none => simp [exec, hs, ht] at h
      | some x =>
        have hh : exec q x s = some r := by simpa [exec, hs, ht] using h
        have hi := ih x s hh
        simpa [interpret, stepAux, stackFn, hs, ht] using hi
  | pop k t q ih =>
    cases hs : s[k]? with
    | none => simp [exec, hs] at h
    | some stk =>
      cases ht : lookup₂ t v (symbolIndex stk.head?) with
      | none => simp [exec, hs, ht] at h
      | some x =>
        have hk : k < s.length := (List.getElem?_eq_some_iff.mp hs).1
        have hh : exec q x (s.set k stk.tail) = some r := by simpa [exec, hs, ht] using h
        have hi := ih x (s.set k stk.tail) hh
        simp [interpret, stepAux, ht, stackFn, hs, ← stackFn_set s k stk.tail hk] at *
        exact hi
  | load t q ih =>
    cases ht : lookup t v with
    | none => simp [exec, ht] at h
    | some x =>
      have hh : exec q x s = some r := by simpa [exec, ht] using h
      simpa [interpret, stepAux, ht] using ih x s hh
  | branch t a b iha ihb =>
    cases ht : lookup t v with
    | none => simp [exec, ht] at h
    | some x =>
      cases x with
      | zero =>
        have hh : exec b v s = some r := by simpa [exec, ht, boolOfNat] using h
        simpa [interpret, stepAux, ht] using ihb v s hh
      | succ x =>
        cases x with
        | zero =>
          have hh : exec a v s = some r := by simpa [exec, ht, boolOfNat] using h
          simpa [interpret, stepAux, ht] using iha v s hh
        | succ x => simp [exec, ht, boolOfNat] at h

example : exec (.push 0 [4] (.goto [7])) 0 [[]] =
    some ⟨some 7, 0, [[4]]⟩ := by decide
example : exec (.push 0 [] .halt) 0 [[]] = none := by decide
example : exec (.push 1 [4] .halt) 0 [[]] = none := by decide
example : exec (.pop 0 [[2]] .halt) 0 [[]] = some ⟨none, 2, [[]]⟩ := by decide
example : exec (.peek 0 [[5, 6]] .halt) 0 [[0]] =
    some ⟨none, 6, [[0]]⟩ := by decide
example : exec (.branch [2] .halt .halt) 0 [] = none := by decide
end Shared.Codes.TM2StatementExecution
