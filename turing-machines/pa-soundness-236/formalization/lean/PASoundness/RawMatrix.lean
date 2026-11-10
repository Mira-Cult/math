import PASoundness.CompactMatrix
import PASoundness.CompactProof

/-!
Exact numeric interfaces of the pinned compact producer. This module connects
pair-encoded environments and raw prefix tests to the functional semantics.
All loops use proved decreasing natural measures; no termination oracle is an
input. The PA/HF interpretation is not supplied by these source-level facts.
-/
namespace PASoundness.RawMatrix

open Cantor CompactMatrix

theorem unpair_snd_lt {z : Nat} (hz : z ≠ 0) : (unpair z).2 < z := by
  have hp := pair_unpair z
  have hs := triangle_ge ((unpair z).1 + (unpair z).2)
  have hz' := unpair_snd_le z
  simp only [pair] at hp
  omega

/-- Literal producer lookup: newest pair binding first; zero environment gives
the default value zero. -/
def lookup (environment name : Nat) : Nat :=
  if environment = 0 then 0 else
    let entry := unpair environment
    let binding := unpair entry.1
    if binding.1 = name then binding.2 else lookup entry.2 name
termination_by environment
decreasing_by exact unpair_snd_lt (by assumption)

@[simp] theorem lookup_zero (name : Nat) : lookup 0 name = 0 := by
  rw [lookup]
  rfl

def push (environment name value : Nat) : Nat := pair (pair name value) environment

theorem pair_zero_iff (a b : Nat) : pair a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hz : pair a b = pair 0 0 := by simpa [pair, triangle] using h
    exact pair_injective hz
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The all-zero sentinel collision is harmless: the erased binding would
assign precisely the existing zero default. -/
theorem lookup_push (environment name value query : Nat) :
    lookup (push environment name value) query =
      if query = name then value else lookup environment query := by
  by_cases hz : push environment name value = 0
  · have h := (pair_zero_iff _ _).mp hz
    have h' := (pair_zero_iff _ _).mp h.1
    rcases h' with ⟨rfl, rfl⟩
    rcases h with ⟨_, rfl⟩
    simp [push, pair, triangle]
  · rw [lookup, if_neg hz]
    simp only [push, unpair_pair]
    by_cases hq : query = name
    · simp [hq]
    · simp [hq, Ne.symm hq]

theorem lookup_push_environment (environment name value : Nat) :
    lookup (push environment name value) = update (lookup environment) name value := by
  funext query
  exact lookup_push environment name value query

/-- The source's left-to-right prefix loop accumulates newest bindings first. -/
def bindEncoded : List Nat → List Nat → Nat → Nat
  | x :: xs, v :: vs, environment => bindEncoded xs vs (push environment x v)
  | _, _, environment => environment

theorem lookup_bindEncoded (names values : List Nat) (environment : Nat) :
    lookup (bindEncoded names values environment) = bind names values (lookup environment) := by
  induction names generalizing values environment with
  | nil => rfl
  | cons x xs ih =>
    cases values with
    | nil => rfl
    | cons v vs =>
      change lookup (bindEncoded xs vs (push environment x v)) =
        bind xs vs (update (lookup environment) x v)
      rw [ih, lookup_push_environment]

def encodeFormula : Formula → Nat
  | .truth => 0
  | .imp a b => CompactProof.imp (encodeFormula a) (encodeFormula b)
  | .member a b => CompactProof.member a b
  | .all x f => CompactProof.allCode x (encodeFormula f)
  | .equal a b => CompactProof.equal a b

/-- The raw numeric decoder is injective on its numeric source, despite the
unreachable AST form `imp truth truth` having the same encoding as truth. -/
theorem encode_decode (code : Nat) : encodeFormula (decode code) = code := by
  induction code using Nat.strong_induction_on with
  | h code ih =>
    by_cases hz : code = 0
    · subst code
      rw [decode]
      rfl
    · have hl : (unpair (code / 4)).1 < code := by
        have := unpair_fst_le (code / 4)
        omega
      have hr : (unpair (code / 4)).2 < code := by
        have := unpair_snd_le (code / 4)
        omega
      have hi₁ := ih _ hl
      have hi₂ := ih _ hr
      rw [decode, if_neg hz]
      by_cases h0 : code % 4 = 0
      · simp only [h0, encodeFormula, CompactProof.imp, hi₁, hi₂, pair_unpair]
        omega
      · by_cases h1 : code % 4 = 1
        · simp only [h1, encodeFormula, CompactProof.member, pair_unpair]
          omega
        · by_cases h2 : code % 4 = 2
          · simp only [h2, encodeFormula, CompactProof.allCode, hi₂, pair_unpair]
            omega
          · have h3 : code % 4 = 3 := by omega
            simp only [h3, encodeFormula, CompactProof.equal, pair_unpair]
            omega

theorem decode_injective : Function.Injective decode := by
  intro a b h
  have h' := congrArg encodeFormula h
  simpa only [encode_decode] using h'

@[simp] theorem encode_falsity : encodeFormula falsity = 1 := rfl

theorem encode_existsAt (x : Nat) (f : Formula) :
    encodeFormula (existsAt x f) = CompactProof.existsCode x (encodeFormula f) := rfl

def peelExistsRaw (f : Nat) : Option (Nat × Nat) :=
  if f % 4 ≠ 0 then none else
    let outer := unpair (f / 4)
    if outer.2 ≠ 1 ∨ outer.1 % 4 ≠ 2 then none else
      let binder := unpair (outer.1 / 4)
      if binder.2 % 4 ≠ 0 then none else
        let inner := unpair (binder.2 / 4)
        if inner.2 ≠ 1 then none else some (binder.1, inner.1)

def peelAllRaw (f : Nat) : Option (Nat × Nat) :=
  if f % 4 ≠ 2 then none else some (unpair (f / 4))

theorem peelExistsRaw_constructor (x f : Nat) :
    peelExistsRaw (CompactProof.existsCode x f) = some (x, f) := by
  simp [peelExistsRaw, CompactProof.existsCode, CompactProof.neg, CompactProof.imp,
    CompactProof.allCode, Nat.mul_add_div]

theorem peelAllRaw_constructor (x f : Nat) :
    peelAllRaw (CompactProof.allCode x f) = some (x, f) := by
  simp [peelAllRaw, CompactProof.allCode, Nat.mul_add_div]

theorem all_code_eq {f : Nat} (h : f % 4 = 2) :
    CompactProof.allCode (unpair (f / 4)).1 (unpair (f / 4)).2 = f := by
  simp only [CompactProof.allCode, pair_unpair]
  omega

theorem peelAllRaw_exact {f x g : Nat} (h : peelAllRaw f = some (x, g)) :
    f = CompactProof.allCode x g := by
  unfold peelAllRaw at h
  split at h
  · cases h
  · rename_i ht
    have ht' : f % 4 = 2 := by omega
    have hu := Option.some.inj h
    have he := all_code_eq ht'
    rw [hu] at he
    exact he.symm

theorem peelExistsRaw_exact {f x g : Nat} (h : peelExistsRaw f = some (x, g)) :
    f = CompactProof.existsCode x g := by
  unfold peelExistsRaw at h
  dsimp only at h
  split at h
  · cases h
  · rename_i ho
    split at h
    · cases h
    · rename_i houter
      split at h
      · cases h
      · rename_i hi
        split at h
        · cases h
        · rename_i hend
          have ho' : f % 4 = 0 := by omega
          have hout : (unpair (f / 4)).2 = 1 := by omega
          have hall : (unpair (f / 4)).1 % 4 = 2 := by omega
          have hi' : (unpair ((unpair (f / 4)).1 / 4)).2 % 4 = 0 := by omega
          have hend' : (unpair ((unpair ((unpair (f / 4)).1 / 4)).2 / 4)).2 = 1 := by omega
          have heq := Option.some.inj h
          have h₁ := CompactProof.imp_decode ho'
          have h₂ := all_code_eq hall
          have h₃ := CompactProof.imp_decode hi'
          have hx := congrArg Prod.fst heq
          have hg := congrArg Prod.snd heq
          dsimp only at hx hg
          rw [hout] at h₁
          rw [hend', hg] at h₃
          rw [hx, ← h₃] at h₂
          rw [← h₂] at h₁
          exact h₁.symm

@[simp] theorem decode_allCode (x f : Nat) :
    decode (CompactProof.allCode x f) = .all x (decode f) := by
  rw [decode]
  simp [CompactProof.allCode, Nat.mul_add_div]

@[simp] theorem decode_one : decode 1 = falsity := by
  rw [decode]
  simp [falsity]

@[simp] theorem decode_neg (f : Nat) :
    decode (CompactProof.neg f) = .imp (decode f) falsity := by
  have hpair : 0 < pair f 1 := by
    have h := unpair_snd_le (pair f 1)
    simp only [unpair_pair] at h
    omega
  rw [decode]
  simp [CompactProof.neg, CompactProof.imp, hpair.ne']

@[simp] theorem decode_existsCode (x f : Nat) :
    decode (CompactProof.existsCode x f) = existsAt x (decode f) := by
  simp only [CompactProof.existsCode, decode_neg, decode_allCode, existsAt]

/-- The numeric tests recognize exactly the typed existential pattern, including
both literal false sentinels. -/
theorem peelExistsRaw_decode (f : Nat) :
    (peelExistsRaw f).map (fun r => (r.1, decode r.2)) =
      peelExists (decode f) := by
  cases hraw : peelExistsRaw f with
  | some r =>
    rcases r with ⟨x,g⟩
    have hf := peelExistsRaw_exact hraw
    rw [hf, decode_existsCode]
    rfl
  | none =>
    cases htyped : peelExists (decode f) with
    | none => rfl
    | some r =>
      rcases r with ⟨x,g⟩
      have he := congrArg encodeFormula (peelExists_exact htyped)
      rw [encode_decode, encode_existsAt] at he
      rw [he, peelExistsRaw_constructor] at hraw
      contradiction

/-- A raw tag-two binder is exactly a typed universal binder. -/
theorem peelAllRaw_decode (f : Nat) :
    (peelAllRaw f).map (fun r => (r.1, decode r.2)) =
      peelAll (decode f) := by
  cases hraw : peelAllRaw f with
  | some r =>
    rcases r with ⟨x,g⟩
    have hf := peelAllRaw_exact hraw
    rw [hf, decode_allCode]
    rfl
  | none =>
    cases htyped : peelAll (decode f) with
    | none => rfl
    | some r =>
      rcases r with ⟨x,g⟩
      have he := congrArg encodeFormula (peelAll_exact htyped)
      simp only [encode_decode, encodeFormula] at he
      rw [he, peelAllRaw_constructor] at hraw
      contradiction

def peelRaw (q : Polarity) (f : Nat) : Option (Nat × Nat) :=
  match q with | .ex => peelExistsRaw f | .all => peelAllRaw f

theorem peelRaw_decode (q : Polarity) (f : Nat) :
    (peelRaw q f).map (fun r => (r.1, decode r.2)) = peel q (decode f) := by
  cases q
  · exact peelExistsRaw_decode f
  · exact peelAllRaw_decode f

def boolNat (b : Bool) : Nat := if b then 1 else 0

/-- Literal repeated-division loop used for HF membership. -/
def bitLoop : Nat → Nat → Nat
  | a, 0 => a % 2
  | a, b+1 => bitLoop (a/2) b

theorem bitLoop_eq (a b : Nat) : bitLoop a b = boolNat (bit a b) := by
  induction b generalizing a with
  | zero =>
    have h : a % 2 < 2 := Nat.mod_lt a (by decide)
    simp only [bitLoop, bit, boolNat, decide_eq_true_eq]
    split <;> omega
  | succ b ih => exact ih (a/2)

/-- Pop right then left; push the source's numeric implication result. The
zero stack sentinel is allowed, exactly as in the producer. -/
def combineValues (values : Nat) : Nat :=
  let right := unpair values
  let left := unpair right.2
  pair (if left.1 = 0 ∨ right.1 ≠ 0 then 1 else 0) left.2

theorem combineValues_pair (a b : Bool) (values : Nat) :
    combineValues (pair (boolNat b) (pair (boolNat a) values)) =
      pair (boolNat ((!a) || b)) values := by
  cases a <;> cases b <;> simp [combineValues, boolNat]

/-- Every ordinary task has positive weight; task one is the delayed binary
combination. Evaluating numeric formula `f` has weight `2*f+2`. -/
def taskWeight (task : Nat) : Nat := if task = 1 then 1 else 2*(task/2)+2

def todoWeight : List Nat → Nat
  | [] => 0
  | task :: todo => taskWeight task + todoWeight todo

theorem taskWeight_pos (task : Nat) : 0 < taskWeight task := by
  unfold taskWeight
  split <;> omega

@[simp] theorem taskWeight_combine : taskWeight 1 = 1 := by rfl

@[simp] theorem taskWeight_formula (f : Nat) : taskWeight (2*f) = 2*f+2 := by
  have h : 2*f ≠ 1 := by omega
  simp [taskWeight, h]

theorem todoWeight_tail (task : Nat) (todo : List Nat) :
    todoWeight todo < todoWeight (task :: todo) := by
  have h := taskWeight_pos task
  simp only [todoWeight]
  omega

/-- Expanding a nonzero implication into left, right, and combine tasks
strictly reduces the pending-work measure, even though the list grows. -/
theorem todoWeight_expand (task : Nat) (todo : List Nat)
    (hne : task ≠ 1) (hz : task / 2 ≠ 0) (htag : (task / 2) % 4 = 0) :
    todoWeight (2*(unpair ((task/2)/4)).1 ::
      2*(unpair ((task/2)/4)).2 :: 1 :: todo) < todoWeight (task :: todo) := by
  have hl := unpair_fst_le ((task/2)/4)
  have hr := unpair_snd_le ((task/2)/4)
  simp only [todoWeight, taskWeight_formula, taskWeight_combine]
  simp only [taskWeight, if_neg hne]
  omega

/-- The producer's pending-task evaluator with its value stack still encoded
by raw Cantor pairs. The list view of `todo` is related to the exact raw loop
below; each recursive call consumes the proved work measure. -/
def runTasks (environment : Nat) (todo : List Nat) (values : Nat) : Option Nat :=
  match todo with
  | [] => some values
  | task :: rest =>
    if task = 1 then runTasks environment rest (combineValues values) else
      let f := task/2
      if f = 0 then runTasks environment rest (pair 1 values) else
        let ab := unpair (f/4)
        if f % 4 = 0 then
          runTasks environment (2*ab.1 :: 2*ab.2 :: 1 :: rest) values
        else if f % 4 = 2 then none else
          let a := lookup environment ab.1
          let b := lookup environment ab.2
          let v := if f % 4 = 1 then bitLoop a b else if a = b then 1 else 0
          runTasks environment rest (pair v values)
termination_by todoWeight todo
decreasing_by
  · exact todoWeight_tail _ _
  · exact todoWeight_tail _ _
  · exact todoWeight_expand _ _ (by assumption) (by assumption) (by assumption)
  · exact todoWeight_tail _ _

@[simp] theorem runTasks_nil (environment values : Nat) :
    runTasks environment [] values = some values := by rw [runTasks]

theorem runTasks_combine (environment values : Nat) (todo : List Nat) :
    runTasks environment (1 :: todo) values =
      runTasks environment todo (combineValues values) := by
  rw [runTasks]
  simp only [↓reduceIte]

theorem runTasks_formula (environment f values : Nat) (todo : List Nat) :
    runTasks environment (2*f :: todo) values =
      if f = 0 then runTasks environment todo (pair 1 values) else
        let ab := unpair (f/4)
        if f % 4 = 0 then
          runTasks environment (2*ab.1 :: 2*ab.2 :: 1 :: todo) values
        else if f % 4 = 2 then none else
          let a := lookup environment ab.1
          let b := lookup environment ab.2
          let v := if f % 4 = 1 then bitLoop a b else if a = b then 1 else 0
          runTasks environment todo (pair v values) := by
  have h : 2*f ≠ 1 := by omega
  rw [runTasks, if_neg h]
  simp only [Nat.mul_div_cancel_left f (by decide : 0 < 2)]

/-- Evaluating one task either rejects a non-QF formula, or pushes exactly one
Boolean result and continues with the unchanged pending tasks. This quantifies
over arbitrary continuations and arbitrary numeric value stacks. -/
theorem runTasks_formula_correct (environment f values : Nat) (todo : List Nat) :
    runTasks environment (2*f :: todo) values =
      (evalQF (lookup environment) (decode f)).bind
        (fun b => runTasks environment todo (pair (boolNat b) values)) := by
  induction f using Nat.strong_induction_on generalizing todo values with
  | h f ih =>
    by_cases hz : f = 0
    · subst f
      rw [runTasks_formula, decode]
      simp only [↓reduceIte, evalQF, Option.bind_some, boolNat]
    · have hl : (unpair (f/4)).1 < f := by
        have h := unpair_fst_le (f/4)
        omega
      have hr : (unpair (f/4)).2 < f := by
        have h := unpair_snd_le (f/4)
        omega
      rw [runTasks_formula, if_neg hz, decode, if_neg hz]
      dsimp only
      by_cases h0 : f % 4 = 0
      · simp only [h0, ↓reduceIte, evalQF]
        rw [ih _ hl]
        cases ha : evalQF (lookup environment) (decode (unpair (f/4)).1) with
        | none => simp only [Option.bind_none]
        | some a =>
          simp only [Option.bind_some]
          rw [ih _ hr]
          cases hb : evalQF (lookup environment) (decode (unpair (f/4)).2) with
          | none => simp only [Option.bind_none]
          | some b =>
            simp only [Option.bind_some]
            rw [runTasks_combine, combineValues_pair]
      · by_cases h1 : f % 4 = 1
        · simp [h1, evalQF, bitLoop_eq]
        · by_cases h2 : f % 4 = 2
          · simp [h2, evalQF]
          · have h3 : f % 4 = 3 := by omega
            simp [h3, evalQF, boolNat]

def cons (head tail : Nat) : Nat := pair head tail + 1

theorem decode_cons (head tail : Nat) :
    Marker.decode (cons head tail) = head :: Marker.decode tail := by
  have h : cons head tail = Marker.encode (head :: Marker.decode tail) := by
    simp only [cons, Marker.encode, Marker.encode_decode]
  rw [h, Marker.decode_encode]

theorem decode_positive {todo : Nat} (h : todo ≠ 0) :
    Marker.decode todo =
      (unpair (todo-1)).1 :: Marker.decode (unpair (todo-1)).2 := by
  have he : todo = cons (unpair (todo-1)).1 (unpair (todo-1)).2 := by
    simp only [cons, pair_unpair]
    omega
  calc
    Marker.decode todo =
        Marker.decode (cons (unpair (todo-1)).1 (unpair (todo-1)).2) := congrArg _ he
    _ = _ := decode_cons _ _

def rawWeight (todo : Nat) : Nat := todoWeight (Marker.decode todo)

theorem rawWeight_tail {todo : Nat} (h : todo ≠ 0) :
    rawWeight (unpair (todo-1)).2 < rawWeight todo := by
  unfold rawWeight
  rw [decode_positive h]
  exact todoWeight_tail _ _

theorem rawWeight_expand {todo : Nat} (h : todo ≠ 0)
    (hne : (unpair (todo-1)).1 ≠ 1)
    (hz : (unpair (todo-1)).1 / 2 ≠ 0)
    (htag : ((unpair (todo-1)).1 / 2) % 4 = 0) :
    rawWeight (cons (2*(unpair (((unpair (todo-1)).1/2)/4)).1)
      (cons (2*(unpair (((unpair (todo-1)).1/2)/4)).2)
        (cons 1 (unpair (todo-1)).2))) < rawWeight todo := by
  unfold rawWeight
  rw [decode_positive h]
  simp only [decode_cons]
  exact todoWeight_expand _ _ hne hz htag

/-- The literal numeric `todo`/`values` loop. Both stacks use exactly the
producer's numeric encodings: `cons = pair + 1` for tasks and bare pairs for
values. Its termination proof covers every numeric state, without a validity
assumption on either stack. -/
def rawLoop (environment todo values : Nat) : Option Nat :=
  if todo = 0 then some values else
    let item := unpair (todo-1)
    let task := item.1
    let rest := item.2
    if task = 1 then rawLoop environment rest (combineValues values) else
      let f := task/2
      if f = 0 then rawLoop environment rest (pair 1 values) else
        let ab := unpair (f/4)
        if f % 4 = 0 then
          rawLoop environment (cons (2*ab.1) (cons (2*ab.2) (cons 1 rest))) values
        else if f % 4 = 2 then none else
          let a := lookup environment ab.1
          let b := lookup environment ab.2
          let v := if f % 4 = 1 then bitLoop a b else if a = b then 1 else 0
          rawLoop environment rest (pair v values)
termination_by rawWeight todo
decreasing_by
  · exact rawWeight_tail (by assumption)
  · exact rawWeight_tail (by assumption)
  · exact rawWeight_expand (by assumption) (by assumption) (by assumption) (by assumption)
  · exact rawWeight_tail (by assumption)

theorem rawLoop_eq_runTasks (environment todo values : Nat) :
    rawLoop environment todo values = runTasks environment (Marker.decode todo) values := by
  fun_induction rawLoop environment todo values with
  | case1 => simp [Marker.decode, Marker.decodeAux]
  | case2 todo values htodo item task rest htask ih =>
    dsimp only [task, item] at htask
    rw [decode_positive htodo, runTasks]
    simpa only [htask, ↓reduceIte] using ih
  | case3 todo values htodo item task rest htask f hzero ih =>
    dsimp only [task, item] at htask
    dsimp only [f, task, item] at hzero
    rw [decode_positive htodo, runTasks]
    simpa only [htask, hzero, ↓reduceIte] using ih
  | case4 todo values htodo item task rest htask f hzero ab htag ih =>
    dsimp only [task, item] at htask
    dsimp only [f, task, item] at hzero htag
    rw [decode_positive htodo, runTasks]
    simpa only [htask, hzero, htag, ↓reduceIte, decode_cons] using ih
  | case5 todo values htodo item task htask f hzero htag hall =>
    dsimp only [task, item] at htask
    dsimp only [f, task, item] at hzero htag hall
    rw [decode_positive htodo, runTasks]
    simp [htask, hzero, hall]
  | case6 todo values htodo item task rest htask f hzero ab htag hall a b v ih =>
    dsimp only [task, item] at htask
    dsimp only [f, task, item] at hzero htag hall
    rw [decode_positive htodo, runTasks]
    simpa [v, a, b, ab, f, task, item, rest, htask, hzero, htag, hall] using ih

/-- Exact source `matrix`: start with the one evaluation task, return `(0,0)`
on a quantified subformula, and otherwise return `(1, top value)`. -/
def matrix (f environment : Nat) : Nat × Nat :=
  match rawLoop environment (cons (2*f) 0) 0 with
  | none => (0,0)
  | some values => (1, (unpair values).1)

/-- Complete source agreement for every code and every encoded environment.
This is independent of PA soundness and of the compact calculus's validity. -/
theorem matrix_eq_evalQF (f environment : Nat) :
    matrix f environment =
      match evalQF (lookup environment) (decode f) with
      | none => (0,0)
      | some b => (1, boolNat b) := by
  rw [matrix, rawLoop_eq_runTasks, decode_cons]
  change (match runTasks environment [2*f] 0 with
    | none => (0,0)
    | some values => (1,(unpair values).1)) = _
  rw [runTasks_formula_correct]
  cases h : evalQF (lookup environment) (decode f) <;>
    simp only [Option.bind_none, Option.bind_some, runTasks_nil, unpair_pair]

/-- Repackage the source's explicit validity flag without identifying an
invalid matrix with a false matrix. -/
def matrixOption (f environment : Nat) : Option Bool :=
  let result := matrix f environment
  if result.1 = 0 then none else some (decide (result.2 ≠ 0))

theorem matrixOption_eq (f environment : Nat) :
    matrixOption f environment = evalQF (lookup environment) (decode f) := by
  rw [matrixOption, matrix_eq_evalQF]
  cases h : evalQF (lookup environment) (decode f) with
  | none => rfl
  | some b => cases b <;> rfl

def polarityAt (i : Nat) : Polarity := if i % 2 = 0 then .ex else .all

theorem polarityAt_succ (i : Nat) : polarityAt (i+1) = (polarityAt i).flip := by
  have h : i % 2 < 2 := Nat.mod_lt i (by decide)
  unfold polarityAt
  by_cases he : i % 2 = 0
  · have hn : (i+1) % 2 ≠ 0 := by omega
    simp [he, hn, Polarity.flip]
  · have hn : (i+1) % 2 = 0 := by omega
    simp [he, hn, Polarity.flip]

/-- The source `record` prefix loop, with `remaining = rank - i`. It checks
the exact coordinate count, uses parity of the original loop counter, and
pushes each binding before advancing. -/
def rawPrefix (i : Nat) : Nat → Nat → Nat → Nat → Option Bool
  | 0, f, environment, xs =>
    if xs = 0 then matrixOption f environment else none
  | remaining+1, f, environment, xs =>
    if xs = 0 then none else
      let entry := unpair (xs-1)
      (peelRaw (polarityAt i) f).bind fun (x,g) =>
        rawPrefix (i+1) remaining g (push environment x entry.1) entry.2

/-- A typed continuation used only to prove the source/normalizer bridge. -/
def evalPrefix (q : Polarity) : Nat → Formula → Environment → List Nat → Option Bool
  | 0, f, environment, [] => evalQF environment f
  | 0, _, _, _ :: _ => none
  | _+1, _, _, [] => none
  | remaining+1, f, environment, value :: values =>
    (peel q f).bind fun (x,g) =>
      evalPrefix q.flip remaining g (update environment x value) values

theorem rawPrefix_eq_evalPrefix (i remaining f environment xs : Nat) :
    rawPrefix i remaining f environment xs =
      evalPrefix (polarityAt i) remaining (decode f) (lookup environment) (Marker.decode xs) := by
  induction remaining generalizing i f environment xs with
  | zero =>
    by_cases hx : xs = 0
    · subst xs
      simp only [rawPrefix, ↓reduceIte, matrixOption_eq]
      rfl
    · rw [rawPrefix, if_neg hx, decode_positive hx]
      rfl
  | succ remaining ih =>
    by_cases hx : xs = 0
    · subst xs
      simp only [rawPrefix, ↓reduceIte]
      rfl
    · rw [rawPrefix, if_neg hx, decode_positive hx, evalPrefix]
      rw [← peelRaw_decode]
      cases hp : peelRaw (polarityAt i) f with
      | none => rfl
      | some r =>
        rcases r with ⟨x,g⟩
        simp only [Option.map_some, Option.bind_some]
        rw [ih, polarityAt_succ, lookup_push_environment]

theorem evalPrefix_eq_normalize (q : Polarity) (n : Nat) (f : Formula)
    (environment : Environment) (xs : List Nat) :
    evalPrefix q n f environment xs =
      if xs.length ≠ n then none else
        (normalize q n f).bind fun r => evalQF (bind r.binders xs environment) r.matrix := by
  induction n generalizing q f environment xs with
  | zero =>
    cases xs with
    | nil =>
      have hv := evalQF_valid f environment
      cases he : evalQF environment f with
      | none =>
        have hq : f.isQF = false := by simpa [he] using hv.symm
        simp [evalPrefix, normalize, CompactMatrix.bind, hq, he]
      | some b =>
        have hq : f.isQF = true := by simpa [he] using hv.symm
        simp [evalPrefix, normalize, CompactMatrix.bind, hq, he]
    | cons x xs => simp [evalPrefix]
  | succ n ih =>
    cases xs with
    | nil => simp [evalPrefix]
    | cons value values =>
      cases hp : peel q f with
      | none => simp [evalPrefix, normalize, hp]
      | some r =>
        rcases r with ⟨x,g⟩
        simp only [evalPrefix, hp, Option.bind_some]
        rw [ih]
        by_cases hlen : values.length = n
        · simp only [hlen, ne_eq, not_true_eq_false, if_false, normalize, hp,
            Option.bind_some, List.length_cons]
          cases hn : normalize q.flip n g <;> simp [CompactMatrix.bind]
        · simp [hlen]

/-- Literal record bit with numeric input tuple. A failed prefix or matrix
returns zero; a valid false matrix returns one. -/
def record (rank certificate xs : Nat) : Nat :=
  match rawPrefix 0 rank (CompactProof.theoremCode certificate) 0 xs with
  | none => 0
  | some truth => if truth then 0 else 1

/-- Exact equality with the normalized producer relation, including malformed
tuple length and normalization failure. No theorem soundness premise occurs. -/
theorem record_eq (rank certificate xs : Nat) :
    record rank certificate xs =
      boolNat (CompactMatrix.record CompactProof.theoremCode rank certificate (Marker.decode xs)) := by
  rw [record, rawPrefix_eq_evalPrefix, evalPrefix_eq_normalize]
  have henv : lookup 0 = (fun _ => 0) := by funext x; exact lookup_zero x
  rw [henv]
  change (match (if (Marker.decode xs).length ≠ rank then none else
    (normalize .ex rank (decode (CompactProof.theoremCode certificate))).bind
      fun r => evalQF (bind r.binders (Marker.decode xs) (fun _ => 0)) r.matrix) with
    | none => 0
    | some truth => if truth then 0 else 1) = _
  unfold CompactMatrix.record
  by_cases hlen : (Marker.decode xs).length ≠ rank
  · simp only [if_pos hlen]
    rfl
  · simp only [if_neg hlen]
    cases h : normalize .ex rank (decode (CompactProof.theoremCode certificate)) with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      cases he : evalQF (bind r.binders (Marker.decode xs) (fun _ => 0)) r.matrix with
      | none => rfl
      | some b => cases b <;> rfl

theorem record_eq_encoded (rank certificate : Nat) (xs : List Nat) :
    record rank certificate (Marker.encode xs) =
      boolNat (CompactMatrix.record CompactProof.theoremCode rank certificate xs) := by
  rw [record_eq, Marker.decode_encode]

theorem boolNat_eq_one (b : Bool) : boolNat b = 1 ↔ b = true := by
  cases b <;> decide

/-- The actual numeric record has precisely the validity-and-false-matrix
meaning, with a separately stated address-length condition. -/
theorem record_spec (rank certificate xs : Nat)
    (hlen : (Marker.decode xs).length = rank) :
    record rank certificate xs = 1 ↔
      CompactMatrix.valid CompactProof.theoremCode rank certificate ∧
        ¬ CompactMatrix.matrixTruth CompactProof.theoremCode rank certificate (Marker.decode xs) := by
  rw [record_eq, boolNat_eq_one]
  exact CompactMatrix.record_spec _ _ _ _ hlen

theorem malformed_tuple_zero (rank certificate xs : Nat)
    (hlen : (Marker.decode xs).length ≠ rank) : record rank certificate xs = 0 := by
  rw [record_eq, CompactMatrix.malformed_tuple_zero _ _ _ _ hlen]
  rfl

theorem quantified_matrix_invalid (x f environment : Nat) :
    matrix (CompactProof.allCode x f) environment = (0,0) := by
  rw [matrix_eq_evalQF, decode_allCode]
  rfl

end PASoundness.RawMatrix
