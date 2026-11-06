import Shared.Codes.TM2Decompose

/-! Uniform primitive-recursive execution of finite numeric TM2 programs.
A positive finite number of node steps executes each whole statement; its
length is bounded by the existing prefix-token count. The encoded program
runner uses the same whole-statement fuel and invalid, timeout, and halt
conventions as `TM2Program.run`. No bit-cost or binary-machine simulation is
proved here. -/
namespace Shared.Codes.TM2Micro
open Shared.Codes.TM2Statements Shared.Codes.TM2StatementExecution Shared.Codes.TM2Decompose
open Shared.Codes.FiniteTables Shared.Codes.TM2FixedComputability Shared.Codes.TM2Primcodable
open Shared.ComplexityBridge.TM2BooleanInput Shared.Codes.TM2Scanner Shared.Codes.TM2Program

abbrev Env := Code × Arg
abbrev Action := Option (ResultRaw ⊕ Env)

def childA (q : Code) : Code := (child₁ q).getD .halt
def childB (q : Code) : Code := (child₂ q).getD .halt

def table1 (n : Nat) : List Nat := Denumerable.ofNat (List Nat) n
def table2 (n : Nat) : List (List Nat) := Denumerable.ofNat (List (List Nat)) n

def haltAction (e : Env) : Action := some (.inl (none,e.2.1,e.2.2))
def gotoAction (e : Env) : Action :=
  (lookup (table1 (slot₁ e.1)) e.2.1).map fun l => .inl (some l,e.2.1,e.2.2)
def pushAction (e : Env) : Action := do
  let stk ← e.2.2[slot₁ e.1]?
  let x ← lookup (table1 (slot₂ e.1)) e.2.1
  return .inr (childA e.1,e.2.1,e.2.2.set (slot₁ e.1) (x::stk))
def peekAction (e : Env) : Action := do
  let stk ← e.2.2[slot₁ e.1]?
  let v ← lookup₂ (table2 (slot₂ e.1)) e.2.1 (symbolIndex stk.head?)
  return .inr (childA e.1,v,e.2.2)
def popAction (e : Env) : Action := do
  let stk ← e.2.2[slot₁ e.1]?
  let v ← lookup₂ (table2 (slot₂ e.1)) e.2.1 (symbolIndex stk.head?)
  return .inr (childA e.1,v,e.2.2.set (slot₁ e.1) stk.tail)
def loadAction (e : Env) : Action := do
  let v ← lookup (table1 (slot₁ e.1)) e.2.1
  return .inr (childA e.1,v,e.2.2)
def branchAction (e : Env) : Action := do
  let x ← lookup (table1 (slot₁ e.1)) e.2.1
  let b ← boolOfNat x
  return .inr (if b then childA e.1 else childB e.1,e.2)

def action (e : Env) : Action :=
  if rootTag e.1 = 0 then haltAction e
  else if rootTag e.1 = 1 then gotoAction e
  else if rootTag e.1 = 2 then pushAction e
  else if rootTag e.1 = 3 then peekAction e
  else if rootTag e.1 = 4 then popAction e
  else if rootTag e.1 = 5 then loadAction e
  else if rootTag e.1 = 6 then branchAction e
  else none

theorem action_halt (v : Nat) (s : Stacks) : action (.halt,v,s) = some (.inl (none,v,s)) := rfl

theorem action_goto (t : List Nat) (v : Nat) (s : Stacks) :
    action (.goto t,v,s) = (lookup t v).map (fun l => .inl (some l,v,s)) := by
  simp [action, gotoAction, table1]

theorem action_push (k : Nat) (t : List Nat) (q : Code) (v : Nat) (s : Stacks) :
    action (.push k t q,v,s) = do
      let stk ← s[k]?
      let x ← lookup t v
      return .inr (q,v,s.set k (x::stk)) := by
  simp [action, pushAction, table1, childA, child₁]

theorem action_peek (k : Nat) (t : List (List Nat)) (q : Code) (v : Nat) (s : Stacks) :
    action (.peek k t q,v,s) = do
      let stk ← s[k]?
      let x ← lookup₂ t v (symbolIndex stk.head?)
      return .inr (q,x,s) := by
  simp [action, peekAction, table2, childA, child₁]

theorem action_pop (k : Nat) (t : List (List Nat)) (q : Code) (v : Nat) (s : Stacks) :
    action (.pop k t q,v,s) = do
      let stk ← s[k]?
      let x ← lookup₂ t v (symbolIndex stk.head?)
      return .inr (q,x,s.set k stk.tail) := by
  simp [action, popAction, table2, childA, child₁]

theorem action_load (t : List Nat) (q : Code) (v : Nat) (s : Stacks) :
    action (.load t q,v,s) = do
      let x ← lookup t v
      return .inr (q,x,s) := by
  simp [action, loadAction, table1, childA, child₁]

theorem action_branch (t : List Nat) (a b : Code) (v : Nat) (s : Stacks) :
    action (.branch t a b,v,s) = do
      let x ← lookup t v
      let b' ← boolOfNat x
      return .inr (if b' then a else b,v,s) := by
  simp [action, branchAction, table1, childA, childB, child₁, child₂]

theorem bindMap_primrec {A B C D : Type} [Primcodable A] [Primcodable B] [Primcodable C] [Primcodable D]
    {f : A → Option B} {g : A × B → Option C} {h : (A × B) × C → D}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec h) :
    Primrec (fun a => (f a).bind fun b => (g (a,b)).map fun c => h ((a,b),c)) :=
  Primrec.option_bind hf (Primrec.option_map hg hh.to₂).to₂

theorem childA_primrec : Primrec childA :=
  Primrec.option_getD.comp child₁_primrec (Primrec.const Code.halt)
theorem childB_primrec : Primrec childB :=
  Primrec.option_getD.comp child₂_primrec (Primrec.const Code.halt)

theorem table1_primrec : Primrec table1 := Primrec.ofNat _
theorem table2_primrec : Primrec table2 := Primrec.ofNat _

theorem haltAction_primrec : Primrec haltAction :=
  Primrec.option_some.comp (Primrec.sumInl.comp (Primrec.pair (Primrec.const none) Primrec.snd))

theorem gotoAction_primrec : Primrec gotoAction := by
  have h : Primrec (fun e : Env => lookup (table1 (slot₁ e.1)) e.2.1) :=
    lookup_primrec.comp (table1_primrec.comp (slot₁_primrec.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)
  have hf : Primrec₂ (fun (e : Env) (l : Nat) => (Sum.inl (some l,e.2.1,e.2.2) : ResultRaw ⊕ Env)) :=
    (Primrec.sumInl.comp (Primrec.pair (Primrec.option_some.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst))).to₂
  exact Primrec.option_map h hf

theorem pushAction_primrec : Primrec pushAction := by
  let P := Env × List Nat
  have hs : Primrec (fun e : Env => e.2.2[slot₁ e.1]?) :=
    Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.snd) (slot₁_primrec.comp Primrec.fst)
  have ht : Primrec (fun p : P => lookup (table1 (slot₂ p.1.1)) p.1.2.1) :=
    lookup_primrec.comp (table1_primrec.comp (slot₂_primrec.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hk : Primrec (fun p : P × Nat => slot₁ p.1.1.1) :=
    slot₁_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hm : Primrec (fun p : P × Nat => p.1.1.2.2.set (slot₁ p.1.1.1) (p.2::p.1.2)) :=
    Primrec.list_set.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.pair hk (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)))
  have ho : Primrec (fun p : P × Nat => (Sum.inr (childA p.1.1.1,p.1.1.2.1,
      p.1.1.2.2.set (slot₁ p.1.1.1) (p.2::p.1.2)) : ResultRaw ⊕ Env)) :=
    Primrec.sumInr.comp (Primrec.pair
      (childA_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) hm))
  apply (bindMap_primrec hs ht ho).of_eq
  intro e
  unfold pushAction
  cases e.2.2[slot₁ e.1]? with
  | none => rfl
  | some stk =>
    simp only [Option.bind_some]
    cases lookup (table1 (slot₂ e.1)) e.2.1 <;> rfl

theorem peekAction_primrec : Primrec peekAction := by
  let P := Env × List Nat
  have hs : Primrec (fun e : Env => e.2.2[slot₁ e.1]?) :=
    Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.snd) (slot₁_primrec.comp Primrec.fst)
  have hi : Primrec (fun p : P => symbolIndex p.2.head?) :=
    symbolIndex_primrec.comp (Primrec.list_head?.comp Primrec.snd)
  have ht : Primrec (fun p : P => lookup₂ (table2 (slot₂ p.1.1)) p.1.2.1 (symbolIndex p.2.head?)) :=
    lookup₂_primrec.comp (Primrec.pair (Primrec.pair
      (table2_primrec.comp (slot₂_primrec.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) hi)
  have ho : Primrec (fun p : P × Nat => (Sum.inr (childA p.1.1.1,p.2,p.1.1.2.2) : ResultRaw ⊕ Env)) :=
    Primrec.sumInr.comp (Primrec.pair
      (childA_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))))
  apply (bindMap_primrec hs ht ho).of_eq
  intro e
  unfold peekAction
  cases e.2.2[slot₁ e.1]? with
  | none => rfl
  | some stk =>
    simp only [Option.bind_some]
    cases h : lookup₂ (table2 (slot₂ e.1)) e.2.1 (symbolIndex stk.head?) <;> simp [h]

theorem popAction_primrec : Primrec popAction := by
  let P := Env × List Nat
  have hs : Primrec (fun e : Env => e.2.2[slot₁ e.1]?) :=
    Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.snd) (slot₁_primrec.comp Primrec.fst)
  have hi : Primrec (fun p : P => symbolIndex p.2.head?) :=
    symbolIndex_primrec.comp (Primrec.list_head?.comp Primrec.snd)
  have ht : Primrec (fun p : P => lookup₂ (table2 (slot₂ p.1.1)) p.1.2.1 (symbolIndex p.2.head?)) :=
    lookup₂_primrec.comp (Primrec.pair (Primrec.pair
      (table2_primrec.comp (slot₂_primrec.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) hi)
  have hk : Primrec (fun p : P × Nat => slot₁ p.1.1.1) :=
    slot₁_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hm : Primrec (fun p : P × Nat => p.1.1.2.2.set (slot₁ p.1.1.1) p.1.2.tail) :=
    Primrec.list_set.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.pair hk (Primrec.list_tail.comp (Primrec.snd.comp Primrec.fst)))
  have ho : Primrec (fun p : P × Nat => (Sum.inr (childA p.1.1.1,p.2,
      p.1.1.2.2.set (slot₁ p.1.1.1) p.1.2.tail) : ResultRaw ⊕ Env)) :=
    Primrec.sumInr.comp (Primrec.pair
      (childA_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) (Primrec.pair Primrec.snd hm))
  apply (bindMap_primrec hs ht ho).of_eq
  intro e
  unfold popAction
  cases e.2.2[slot₁ e.1]? with
  | none => rfl
  | some stk =>
    simp only [Option.bind_some]
    cases h : lookup₂ (table2 (slot₂ e.1)) e.2.1 (symbolIndex stk.head?) <;> simp [h]

theorem loadAction_primrec : Primrec loadAction := by
  have ht : Primrec (fun e : Env => lookup (table1 (slot₁ e.1)) e.2.1) :=
    lookup_primrec.comp (table1_primrec.comp (slot₁_primrec.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)
  have hf : Primrec₂ (fun (e : Env) (v : Nat) => (Sum.inr (childA e.1,v,e.2.2) : ResultRaw ⊕ Env)) :=
    (Primrec.sumInr.comp (Primrec.pair (childA_primrec.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).to₂
  apply (Primrec.option_map ht hf).of_eq
  intro e
  unfold loadAction
  cases lookup (table1 (slot₁ e.1)) e.2.1 <;> rfl

theorem branchAction_primrec : Primrec branchAction := by
  let P := Env × Nat
  have ht : Primrec (fun e : Env => lookup (table1 (slot₁ e.1)) e.2.1) :=
    lookup_primrec.comp (table1_primrec.comp (slot₁_primrec.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)
  have hb : Primrec (fun p : P => boolOfNat p.2) := boolOfNat_primrec.comp Primrec.snd
  have hq : Primrec (fun p : P × Bool => if p.2 then childA p.1.1.1 else childB p.1.1.1) := by
    have h := Primrec.cond (Primrec.snd : Primrec (fun p : P × Bool => p.2))
      (childA_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (childB_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
    apply h.of_eq
    intro p
    cases p.2 <;> rfl
  have ho : Primrec (fun p : P × Bool => (Sum.inr
      (if p.2 then childA p.1.1.1 else childB p.1.1.1,p.1.1.2) : ResultRaw ⊕ Env)) :=
    Primrec.sumInr.comp (Primrec.pair hq (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  apply (bindMap_primrec ht hb ho).of_eq
  intro e
  unfold branchAction
  cases lookup (table1 (slot₁ e.1)) e.2.1 with
  | none => rfl
  | some x =>
    simp only [Option.bind_some]
    cases h : boolOfNat x <;> simp [h]

theorem action_primrec : Primrec action := by
  have ht (n : Nat) : PrimrecPred (fun e : Env => rootTag e.1 = n) :=
    Primrec.eq.comp (rootTag_primrec.comp Primrec.fst) (Primrec.const n)
  exact Primrec.ite (ht 0) haltAction_primrec
    (Primrec.ite (ht 1) gotoAction_primrec
    (Primrec.ite (ht 2) pushAction_primrec
    (Primrec.ite (ht 3) peekAction_primrec
    (Primrec.ite (ht 4) popAction_primrec
    (Primrec.ite (ht 5) loadAction_primrec
    (Primrec.ite (ht 6) branchAction_primrec (Primrec.const none)))))))

/-- Finished and invalid states are absorbing; active states execute one
statement node. -/
def step : Action → Action
  | none => none
  | some (.inl r) => some (.inl r)
  | some (.inr e) => action e

theorem step_primrec : Primrec step := by
  have hsum : Primrec (fun s : ResultRaw ⊕ Env => match s with
      | .inl r => (some (.inl r) : Action)
      | .inr e => action e) := by
    have h := Primrec.sumCasesOn (Primrec.id : Primrec (fun s : ResultRaw ⊕ Env => s))
      (Primrec.option_some.comp (Primrec.sumInl.comp Primrec.snd)).to₂
      (action_primrec.comp Primrec.snd).to₂
    exact h.of_eq (by intro s; cases s <;> rfl)
  have h := Primrec.option_casesOn (Primrec.id : Primrec (fun s : Action => s))
    (Primrec.const none) (hsum.comp Primrec.snd).to₂
  apply h.of_eq
  intro s
  cases s with
  | none => rfl
  | some x => cases x <;> rfl

def runNodes (fuel : Nat) (q : Code) (a : Arg) : Action :=
  step^[fuel] (some (.inr (q,a)))

theorem runNodes_none (n : Nat) : step^[n] none = none := Function.iterate_fixed rfl n

theorem runNodes_done (n : Nat) (r : ResultRaw) :
    step^[n] (some (.inl r)) = some (.inl r) := Function.iterate_fixed rfl n

theorem runNodes_succ (n : Nat) (q : Code) (a : Arg) :
    runNodes (n+1) q a = step^[n] (action (q,a)) := by
  simp [runNodes, Function.iterate_succ_apply, step]

theorem runNodes_correct (q : Code) (fuel : Nat) (a : Arg)
    (hf : nodeCount q ≤ fuel) :
    runNodes fuel q a = (execRaw q a).map Sum.inl := by
  induction q generalizing fuel a with
  | halt =>
    cases fuel with
    | zero => simp [nodeCount] at hf
    | succ f =>
      rcases a with ⟨v,s⟩
      simp [runNodes_succ, action_halt, execRaw, runNodes_done]
  | goto t =>
    cases fuel with
    | zero => simp [nodeCount] at hf
    | succ f =>
      rcases a with ⟨v,s⟩
      rw [runNodes_succ, action_goto]
      cases h : lookup t v <;> simp [execRaw, h, runNodes_none, runNodes_done]
  | push k t q ih =>
    cases fuel with
    | zero => simp [nodeCount] at hf
    | succ f =>
      rcases a with ⟨v,s⟩
      have hh : nodeCount q ≤ f := by simp [nodeCount] at hf; omega
      rw [runNodes_succ, action_push]
      cases hs : s[k]? with
      | none => simp [hs, execRaw, runNodes_none]
      | some stk =>
        cases ht : lookup t v with
        | none => simp [hs, ht, execRaw, runNodes_none]
        | some x =>
          simpa [hs, ht, execRaw, runNodes] using ih f (v,s.set k (x::stk)) hh
  | peek k t q ih =>
    cases fuel with
    | zero => simp [nodeCount] at hf
    | succ f =>
      rcases a with ⟨v,s⟩
      have hh : nodeCount q ≤ f := by simp [nodeCount] at hf; omega
      rw [runNodes_succ, action_peek]
      cases hs : s[k]? with
      | none => simp [hs, execRaw, runNodes_none]
      | some stk =>
        cases ht : lookup₂ t v (symbolIndex stk.head?) with
        | none => simp [hs, ht, execRaw, runNodes_none]
        | some x => simpa [hs, ht, execRaw, runNodes] using ih f (x,s) hh
  | pop k t q ih =>
    cases fuel with
    | zero => simp [nodeCount] at hf
    | succ f =>
      rcases a with ⟨v,s⟩
      have hh : nodeCount q ≤ f := by simp [nodeCount] at hf; omega
      rw [runNodes_succ, action_pop]
      cases hs : s[k]? with
      | none => simp [hs, execRaw, runNodes_none]
      | some stk =>
        cases ht : lookup₂ t v (symbolIndex stk.head?) with
        | none => simp [hs, ht, execRaw, runNodes_none]
        | some x => simpa [hs, ht, execRaw, runNodes] using ih f (x,s.set k stk.tail) hh
  | load t q ih =>
    cases fuel with
    | zero => simp [nodeCount] at hf
    | succ f =>
      rcases a with ⟨v,s⟩
      have hh : nodeCount q ≤ f := by simp [nodeCount] at hf; omega
      rw [runNodes_succ, action_load]
      cases ht : lookup t v with
      | none => simp [ht, execRaw, runNodes_none]
      | some x => simpa [ht, execRaw, runNodes] using ih f (x,s) hh
  | branch t left right iha ihb =>
    cases fuel with
    | zero => simp [nodeCount] at hf
    | succ f =>
      rcases a with ⟨v,s⟩
      have ha : nodeCount left ≤ f := by simp [nodeCount] at hf; omega
      have hb : nodeCount right ≤ f := by simp [nodeCount] at hf; omega
      rw [runNodes_succ, action_branch]
      cases ht : lookup t v with
      | none => simp [ht, execRaw, runNodes_none]
      | some x =>
        cases hv : boolOfNat x with
        | none => simp [ht, hv, execRaw, runNodes_none]
        | some v' =>
          cases v' with
          | false => simpa [ht, hv, execRaw, runNodes] using ihb f (v,s) hb
          | true => simpa [ht, hv, execRaw, runNodes] using iha f (v,s) ha

def completed : Action → Option ResultRaw
  | some (.inl r) => some r
  | _ => none

theorem completed_primrec : Primrec completed := by
  have hs : Primrec (fun s : ResultRaw ⊕ Env => match s with
      | .inl r => some r
      | .inr _ => (none : Option ResultRaw)) := by
    have h := Primrec.sumCasesOn (Primrec.id : Primrec (fun s : ResultRaw ⊕ Env => s))
      (Primrec.option_some.comp Primrec.snd).to₂ (Primrec.const none).to₂
    exact h.of_eq (by intro s; cases s <;> rfl)
  have h := Primrec.option_casesOn (Primrec.id : Primrec (fun s : Action => s))
    (Primrec.const none) (hs.comp Primrec.snd).to₂
  apply h.of_eq
  intro s
  cases s with
  | none => rfl
  | some x => cases x <;> rfl

def evaluate (e : Env) : Option ResultRaw :=
  completed (runNodes (tokens e.1).length e.1 e.2)

theorem evaluate_primrec : Primrec evaluate := by
  have hf : Primrec (fun e : Env => (tokens e.1).length) :=
    Primrec.list_length.comp (tokens_primrec.comp Primrec.fst)
  have hi : Primrec (fun e : Env => (some (.inr e) : Action)) :=
    Primrec.option_some.comp (Primrec.sumInr.comp Primrec.id)
  have hs := Primrec.nat_iterate hf hi (step_primrec.comp Primrec.snd).to₂
  exact completed_primrec.comp hs

theorem evaluate_eq (q : Code) (a : Arg) : evaluate (q,a) = execRaw q a := by
  unfold evaluate
  rw [runNodes_correct q (tokens q).length a (nodeCount_le_length q)]
  cases execRaw q a <;> rfl

theorem execRaw_uniform_primrec : Primrec (fun e : Env => execRaw e.1 e.2) :=
  evaluate_primrec.of_eq (fun e => evaluate_eq e.1 e.2)

theorem execRaw_uniform_computable : Computable (fun e : Env => execRaw e.1 e.2) :=
  execRaw_uniform_primrec.to_comp

theorem dispatch_as_bind (p : Program) (l : Nat) (a : Arg) :
    dispatch p l a = (p[l]?).bind fun q => execRaw q a := by
  rcases a with ⟨v,s⟩
  rw [dispatch_eq]
  cases p[l]? <;> simp [execRaw_eq]

theorem dispatch_uniform_primrec :
    Primrec (fun x : Program × Nat × Arg => dispatch x.1 x.2.1 x.2.2) := by
  let P := Program × Nat × Arg
  have hl : Primrec (fun x : P => x.1[x.2.1]?) :=
    Primrec.list_getElem?.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have he : Primrec₂ (fun (x : P) (q : Code) => execRaw q x.2.2) :=
    (execRaw_uniform_primrec.comp (Primrec.pair Primrec.snd
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).to₂
  have h := Primrec.option_bind hl he
  apply h.of_eq
  intro x
  exact (dispatch_as_bind x.1 x.2.1 x.2.2).symm

theorem advance_uniform_primrec :
    Primrec (fun x : Program × Shared.Codes.TM2FixedComputability.Status => advance x.1 x.2) := by
  let P := Program × ResultRaw
  have hl : Primrec (fun p : P => p.2.1.getD 0) :=
    Primrec.option_getD.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)
  have hd : Primrec (fun p : P => dispatch p.1 (p.2.1.getD 0) p.2.2) :=
    dispatch_uniform_primrec.comp (Primrec.pair Primrec.fst (Primrec.pair hl (Primrec.snd.comp Primrec.snd)))
  have hi : Primrec (fun r : ResultRaw => (r.1.isNone,r)) := by
    have h := Primrec.pair (Primrec.not.comp (Primrec.option_isSome.comp
      (Primrec.fst : Primrec (fun r : ResultRaw => r.1)))) Primrec.id
    apply h.of_eq
    intro r
    cases r.1 <;> rfl
  have hm : Primrec (fun p : P => (dispatch p.1 (p.2.1.getD 0) p.2.2).map
      (fun (d : ResultRaw) => (d.1.isNone,d))) := Primrec.option_map hd (hi.comp Primrec.snd).to₂
  have hn : Primrec (fun p : P => match p.2.1 with
      | none => some (true,p.2)
      | some l => (dispatch p.1 l p.2.2).map fun (d : ResultRaw) => (d.1.isNone,d)) := by
    have h := Primrec.option_casesOn (Primrec.fst.comp (Primrec.snd : Primrec (fun p : P => p.2)))
      (Primrec.option_some.comp (Primrec.pair (Primrec.const true) Primrec.snd)) (hm.comp Primrec.fst).to₂
    apply h.of_eq
    intro p
    rcases p with ⟨p,o,v,s⟩
    cases o <;> rfl
  have hb : Primrec (fun p : Program × (Bool × ResultRaw) => if p.2.1 then some (true,p.2.2) else
      match p.2.2.1 with
      | none => some (true,p.2.2)
      | some l => (dispatch p.1 l p.2.2.2).map fun (d : ResultRaw) => (d.1.isNone,d)) := by
    have h := Primrec.cond (Primrec.fst.comp (Primrec.snd : Primrec (fun p : Program × (Bool × ResultRaw) => p.2)))
      (Primrec.option_some.comp (Primrec.pair (Primrec.const true) (Primrec.snd.comp Primrec.snd)))
      (hn.comp (Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd)))
    apply h.of_eq
    intro p
    cases p.2.1 <;> rfl
  have h := Primrec.option_casesOn (Primrec.snd : Primrec (fun x : Program × Shared.Codes.TM2FixedComputability.Status => x.2))
    (Primrec.const none) (hb.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂
  apply h.of_eq
  intro x
  rcases x with ⟨p,s⟩
  cases s with
  | none => rfl
  | some v => rcases v with ⟨b,r⟩; cases b <;> rfl

theorem runRaw_uniform_primrec : Primrec (fun x : (Program × Nat) × ResultRaw => runRaw x.1.1 x.1.2 x.2) := by
  have hi : Primrec (fun x : (Program × Nat) × ResultRaw => initial x.2) :=
    initial_primrec.comp Primrec.snd
  have hs : Primrec₂ (fun (x : (Program × Nat) × ResultRaw) (s : Shared.Codes.TM2FixedComputability.Status) =>
      advance x.1.1 s) :=
    (advance_uniform_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)).to₂
  exact Primrec.nat_iterate (Primrec.snd.comp Primrec.fst) hi hs

/-- Decode a finite program and run it under a whole-block clock. A failed
decode or invalid checked execution returns `none`. -/
def runEncoded (x : (Nat × Nat) × ResultRaw) : Shared.Codes.TM2FixedComputability.Status :=
  (decodeProgram x.1.1).bind fun p => runRaw p x.1.2 x.2

theorem runEncoded_primrec : Primrec runEncoded := by
  have hd : Primrec (fun x : (Nat × Nat) × ResultRaw => decodeProgram x.1.1) :=
    decodeProgram_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hr : Primrec₂ (fun (x : (Nat × Nat) × ResultRaw) (p : Program) => runRaw p x.1.2 x.2) :=
    (runRaw_uniform_primrec.comp (Primrec.pair
      (Primrec.pair Primrec.snd (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.fst))).to₂
  exact Primrec.option_bind hd hr

theorem runEncoded_computable : Computable runEncoded := runEncoded_primrec.to_comp

theorem runEncoded_invalid (n fuel : Nat) (r : ResultRaw) (h : decodeProgram n = none) :
    runEncoded ((n,fuel),r) = none := by simp [runEncoded, h]

theorem runEncoded_of_decode (n : Nat) (p : Program) (fuel : Nat) (c : Result)
    (h : decodeProgram n = some p) :
    runEncoded ((n,fuel),resultRaw c) = outcomeRaw (run p fuel c) := by
  simp [runEncoded, h, runRaw_eq]

theorem runEncoded_correct (p : Program) (fuel : Nat) (c : Result) :
    runEncoded ((Encodable.encode p,fuel), resultRaw c) = outcomeRaw (run p fuel c) := by
  simp [runEncoded, decodeProgram, runRaw_eq]

example : evaluate (.pop 0 [[2]] .halt,0,[[]]) = some (none,2,[[]]) := by
  simp [evaluate_eq, execRaw, lookup₂, symbolIndex]
example : evaluate (.push 1 [4] .halt,0,[[]]) = none := by
  simp [evaluate_eq, execRaw]
example : evaluate (.branch [2] .halt .halt,0,[]) = none := by
  simp [evaluate_eq, execRaw, boolOfNat, lookup]
example : evaluate (.push 0 [4] (.goto [7]),0,[[]]) = some (some 7,0,[[4]]) := by
  simp [evaluate_eq, execRaw, lookup]
example : runEncoded ((Encodable.encode ([.halt] : Program),0),(some 0,0,[])) =
    some (false,(some 0,0,[])) := by
  simpa [outcomeRaw, resultRaw, run] using runEncoded_correct [.halt] 0 ⟨some 0,0,[]⟩
example : runEncoded ((Encodable.encode ([.halt] : Program),1),(some 0,0,[])) =
    some (true,(none,0,[])) := by
  simpa [outcomeRaw, resultRaw, run, exec] using runEncoded_correct [.halt] 1 ⟨some 0,0,[]⟩

end Shared.Codes.TM2Micro
