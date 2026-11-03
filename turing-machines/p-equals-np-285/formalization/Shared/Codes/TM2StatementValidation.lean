import Shared.Codes.TM2StatementExecution

/-! An executable local validator and completeness for one numeric TM2
statement block. A uniform symbol bound is assumed; normalization coverage,
whole-machine execution, recursion-theoretic computability and cost bounds
remain separate obligations. -/
namespace Shared.Codes.TM2StatementValidation
open Shared.Codes.TM2Statements Shared.Codes.TM2StatementExecution Shared.Codes.FiniteTables

/-- An executable rectangular-table check; unused excess rows are allowed. -/
def unaryValid (t : List Nat) (inputs outputs : Nat) : Bool :=
  (List.range inputs).all fun i => match lookup t i with
    | some x => x < outputs
    | none => false

def binaryValid (t : List (List Nat)) (rows cols outputs : Nat) : Bool :=
  (List.range rows).all fun i => (List.range cols).all fun j =>
    match lookup₂ t i j with
    | some x => x < outputs
    | none => false

theorem unary_get {t : List Nat} {inputs outputs i : Nat}
    (h : unaryValid t inputs outputs = true) (hi : i < inputs) :
    ∃ x, lookup t i = some x ∧ x < outputs := by
  have hm := (List.all_eq_true.mp h) i (List.mem_range.mpr hi)
  cases ht : lookup t i with
  | none => simp [ht] at hm
  | some x => exact ⟨x, rfl, by simpa [ht] using hm⟩

theorem binary_get {t : List (List Nat)} {rows cols outputs i j : Nat}
    (h : binaryValid t rows cols outputs = true) (hi : i < rows) (hj : j < cols) :
    ∃ x, lookup₂ t i j = some x ∧ x < outputs := by
  have hm := (List.all_eq_true.mp h) i (List.mem_range.mpr hi)
  have hn := (List.all_eq_true.mp hm) j (List.mem_range.mpr hj)
  cases ht : lookup₂ t i j with
  | none => simp [ht] at hn
  | some x => exact ⟨x, rfl, by simpa [ht] using hn⟩

/-- A common finite alphabet bound is used for all numeric stacks. A later
normalization must prove coverage of heterogeneous TM2 alphabets. -/
def valid (ks states symbols labels : Nat) : Code → Bool
  | .halt => true
  | .goto t => unaryValid t states labels
  | .push k t q => (k < ks) && unaryValid t states symbols && valid ks states symbols labels q
  | .peek k t q => (k < ks) && binaryValid t states (symbols + 1) states && valid ks states symbols labels q
  | .pop k t q => (k < ks) && binaryValid t states (symbols + 1) states && valid ks states symbols labels q
  | .load t q => unaryValid t states states && valid ks states symbols labels q
  | .branch t a b => unaryValid t states 2 && valid ks states symbols labels a && valid ks states symbols labels b

def stacksValid (ks symbols : Nat) (s : Stacks) : Prop :=
  s.length = ks ∧ ∀ stk ∈ s, ∀ x ∈ stk, x < symbols

def resultValid (ks states symbols labels : Nat) (r : Result) : Prop :=
  r.state < states ∧ stacksValid ks symbols r.memory ∧
    ∀ l, r.label = some l → l < labels

theorem valid_set {ks symbols : Nat} {s : Stacks} (hs : stacksValid ks symbols s)
    (k : Nat) (stk : List Nat) (hstk : ∀ x ∈ stk, x < symbols) :
    stacksValid ks symbols (s.set k stk) := by
  refine ⟨by simpa using hs.1, ?_⟩
  intro xs hxs x hx
  rcases List.mem_or_eq_of_mem_set hxs with hold | heq
  · exact hs.2 xs hold x hx
  · subst xs; exact hstk x hx

theorem stack_at {ks symbols : Nat} {s : Stacks} (hs : stacksValid ks symbols s)
    {k : Nat} (hk : k < ks) : ∃ stk, s[k]? = some stk ∧ ∀ x ∈ stk, x < symbols := by
  have hks : k < s.length := by simpa [hs.1] using hk
  let stk := s[k]
  have hget : s[k]? = some stk := by simp [stk, hks]
  have hm : stk ∈ s := List.getElem_mem hks
  exact ⟨stk, hget, hs.2 stk hm⟩

theorem symbolIndex_bound {symbols : Nat} (stk : List Nat)
    (hs : ∀ x ∈ stk, x < symbols) : symbolIndex stk.head? < symbols + 1 := by
  cases stk with
  | nil => simp [symbolIndex]
  | cons a xs =>
    have ha : a < symbols := hs a (by simp)
    simp [symbolIndex]
    omega

/-- Validated finite tables finish a complete statement block and preserve the
state, stack and label ranges. -/
theorem exec_complete (q : Code) (ks states symbols labels : Nat)
    (hv : valid ks states symbols labels q = true)
    (v : Nat) (s : Stacks) (hstate : v < states) (hs : stacksValid ks symbols s) :
    ∃ r, exec q v s = some r ∧ resultValid ks states symbols labels r := by
  induction q generalizing v s with
  | halt =>
    refine ⟨⟨none, v, s⟩, rfl, hstate, hs, ?_⟩
    simp
  | goto t =>
    obtain ⟨l, hl, hlt⟩ := unary_get (by simpa [valid] using hv) hstate
    refine ⟨⟨some l, v, s⟩, ?_, hstate, hs, ?_⟩
    · simp [exec, hl]
    · intro x hx; cases hx; exact hlt
  | push k t q ih =>
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hk, ht⟩, hq⟩ := hv
    obtain ⟨stk, hget, hstk⟩ := stack_at hs hk
    obtain ⟨x, hx, hxb⟩ := unary_get ht hstate
    have hs' : stacksValid ks symbols (s.set k (x :: stk)) :=
      valid_set hs k (x :: stk) (by intro y hy; simp only [List.mem_cons] at hy; rcases hy with rfl | hy; exact hxb; exact hstk y hy)
    obtain ⟨r, hr, good⟩ := ih hq v (s.set k (x :: stk)) hstate hs'
    exact ⟨r, by simpa [exec, hget, hx] using hr, good⟩
  | peek k t q ih =>
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hk, ht⟩, hq⟩ := hv
    obtain ⟨stk, hget, hstk⟩ := stack_at hs hk
    obtain ⟨x, hx, hxb⟩ := binary_get ht hstate (symbolIndex_bound stk hstk)
    obtain ⟨r, hr, good⟩ := ih hq x s hxb hs
    exact ⟨r, by simpa [exec, hget, hx] using hr, good⟩
  | pop k t q ih =>
    simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hk, ht⟩, hq⟩ := hv
    obtain ⟨stk, hget, hstk⟩ := stack_at hs hk
    obtain ⟨x, hx, hxb⟩ := binary_get ht hstate (symbolIndex_bound stk hstk)
    have hs' : stacksValid ks symbols (s.set k stk.tail) :=
      valid_set hs k stk.tail (by intro y hy; exact hstk y (List.mem_of_mem_tail hy))
    obtain ⟨r, hr, good⟩ := ih hq x (s.set k stk.tail) hxb hs'
    exact ⟨r, by simpa [exec, hget, hx] using hr, good⟩
  | load t q ih =>
    simp only [valid, Bool.and_eq_true] at hv
    obtain ⟨ht, hq⟩ := hv
    obtain ⟨x, hx, hxb⟩ := unary_get ht hstate
    obtain ⟨r, hr, good⟩ := ih hq x s hxb hs
    exact ⟨r, by simpa [exec, hx] using hr, good⟩
  | branch t a b iha ihb =>
    simp only [valid, Bool.and_eq_true] at hv
    obtain ⟨⟨ht, ha⟩, hb⟩ := hv
    obtain ⟨x, hx, hxb⟩ := unary_get ht hstate
    have : x = 0 ∨ x = 1 := by omega
    rcases this with rfl | rfl
    · obtain ⟨r, hr, good⟩ := ihb hb v s hstate hs
      exact ⟨r, by simpa [exec, hx, boolOfNat] using hr, good⟩
    · obtain ⟨r, hr, good⟩ := iha ha v s hstate hs
      exact ⟨r, by simpa [exec, hx, boolOfNat] using hr, good⟩

/-- The executable check gives both a successful result and exact TM2
statement-block behavior, with all numeric bounds preserved. -/
theorem validated_block_correct (q : Code) (ks states symbols labels : Nat)
    (hv : valid ks states symbols labels q = true)
    (v : Nat) (s : Stacks) (hstate : v < states) (hs : stacksValid ks symbols s) :
    ∃ r, exec q v s = some r ∧ resultValid ks states symbols labels r ∧
      Turing.TM2.stepAux (interpret q) v (stackFn s) = erase r := by
  obtain ⟨r, hr, hb⟩ := exec_complete q ks states symbols labels hv v s hstate hs
  exact ⟨r, hr, hb, exec_sound q v s r hr⟩

example : valid 1 1 1 1 (.push 0 [0] (.goto [0])) = true := by decide
example : valid 1 1 1 1 (.push 0 [] .halt) = false := by decide
example : valid 1 1 1 1 (.push 1 [0] .halt) = false := by decide
example : valid 1 1 1 1 (.peek 0 [[0]] .halt) = false := by decide
example : valid 1 1 1 1 (.branch [2] .halt .halt) = false := by decide

end Shared.Codes.TM2StatementValidation
