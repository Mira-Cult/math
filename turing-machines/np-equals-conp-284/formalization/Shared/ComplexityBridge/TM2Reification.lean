import Shared.Codes.TM2ProgramHalt

/-! Classical existence reification of finite function-valued TM2 machines
into validated finite numeric programs. Runtime tables and the checked runner
are finite data; reifying arbitrary Lean functions is not executable. Clocks
count whole TM2 statement blocks, not bit operations. The reverse simulation, bit-cost bounds, and beeper compilation remain open.
`TM2Primcodable` and `TM2Micro` prove decoder and interpreter computability. -/
namespace Shared.ComplexityBridge.TM2Reification
open Turing.TM2
open Shared.Codes.FiniteTables Shared.Codes.TM2Statements Shared.Codes.TM2StatementExecution
open Shared.Codes.TM2StatementValidation

/-- Mathematical numberings of the finite types in a normalized TM2. Stack
alphabets may have different cardinalities, bounded by a common numeric size. -/
structure Numbering {K : Type} (Γ : K → Type) (Λ σ : Type) where
  stackCount : Nat
  states : Nat
  labels : Nat
  symbols : Nat
  stack : K ≃ Fin stackCount
  state : σ ≃ Fin states
  label : Λ ≃ Fin labels
  symbolCount : K → Nat
  symbol : ∀ k, Γ k ≃ Fin (symbolCount k)
  symbol_bound : ∀ k, symbolCount k ≤ symbols

variable {K Λ σ : Type} {Γ : K → Type} (N : Numbering Γ Λ σ)

def encodedHead (k : K) (o : Option (Γ k)) : Nat :=
  symbolIndex (o.map fun x => (N.symbol k x).val)

/-- The extra columns beyond an individual stack alphabet are rejected by
this partial decoder; table reification uses a bounded default there. -/
def decodeHead (k : K) : Nat → Option (Option (Γ k))
  | 0 => some none
  | n + 1 => if h : n < N.symbolCount k then some (some ((N.symbol k).symm ⟨n, h⟩)) else none

theorem encodedHead_lt (k : K) (o : Option (Γ k)) : encodedHead N k o < N.symbols + 1 := by
  cases o with
  | none => simp [encodedHead, symbolIndex]
  | some x =>
    have hx := (N.symbol k x).isLt
    have hb := N.symbol_bound k
    simp [encodedHead, symbolIndex]
    omega

theorem decodeHead_encoded (k : K) (o : Option (Γ k)) :
    decodeHead N k (encodedHead N k o) = some o := by
  cases o with
  | none => rfl
  | some x => simp [decodeHead, encodedHead, symbolIndex, (N.symbol k x).isLt]

def unaryTable {α : Type} (encodeOut : α → Nat) (f : σ → α) : List Nat :=
  table₁ fun i => encodeOut (f (N.state.symm i))

def readTable (k : K) (f : σ → Option (Γ k) → σ) : List (List Nat) :=
  table₂ fun i : Fin N.states => fun j : Fin (N.symbols + 1) =>
    match decodeHead N k j.val with
    | none => i.val
    | some x => (N.state (f (N.state.symm i) x)).val

theorem unaryTable_lookup {α : Type} (enc : α → Nat) (f : σ → α) (v : σ) :
    lookup (unaryTable N enc f) (N.state v).val = some (enc (f v)) := by
  simp [unaryTable]

theorem readTable_lookup (k : K) (f : σ → Option (Γ k) → σ) (v : σ) (o : Option (Γ k)) :
    lookup₂ (readTable N k f) (N.state v).val (encodedHead N k o) = some (N.state (f v o)).val := by
  let j : Fin (N.symbols + 1) := ⟨encodedHead N k o, encodedHead_lt N k o⟩
  have h := lookup_table₂ (fun i : Fin N.states => fun j : Fin (N.symbols + 1) =>
    match decodeHead N k j.val with
    | none => i.val
    | some x => (N.state (f (N.state.symm i) x)).val) (N.state v) j
  simpa [readTable, j, decodeHead_encoded] using h

theorem unary_table_valid {α : Type} (enc : α → Nat) (f : σ → α) (bound : Nat)
    (h : ∀ a, enc a < bound) : unaryValid (unaryTable N enc f) N.states bound = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hi' : i < N.states := List.mem_range.mp hi
  have he := lookup_table₁ (fun i : Fin N.states => enc (f (N.state.symm i))) ⟨i, hi'⟩
  simpa [unaryTable, he] using h (f (N.state.symm ⟨i, hi'⟩))

theorem read_table_valid (k : K) (f : σ → Option (Γ k) → σ) :
    binaryValid (readTable N k f) N.states (N.symbols + 1) N.states = true := by
  apply List.all_eq_true.mpr
  intro i hi
  apply List.all_eq_true.mpr
  intro j hj
  have hi' : i < N.states := List.mem_range.mp hi
  have hj' : j < N.symbols + 1 := List.mem_range.mp hj
  let ii : Fin N.states := ⟨i, hi'⟩
  let jj : Fin (N.symbols + 1) := ⟨j, hj'⟩
  have he := lookup_table₂ (fun a : Fin N.states => fun b : Fin (N.symbols + 1) =>
    match decodeHead N k b.val with
    | none => a.val
    | some x => (N.state (f (N.state.symm a) x)).val) ii jj
  change (match lookup₂ (readTable N k f) i j with | some x => decide (x < N.states) | none => false) = true
  rw [show lookup₂ (readTable N k f) i j = some (match decodeHead N k j with
    | none => i | some x => (N.state (f (N.state.symm ii) x)).val) by simpa [readTable, ii, jj] using he]
  cases h : decodeHead N k j with
  | none => simpa [h] using hi'
  | some x => simpa [h] using (N.state (f (N.state.symm ii) x)).isLt

/-- Tabulate all local functions in a finite statement. This is a mathematical
construction on an arbitrary function-valued statement, not a runtime
reifier of Lean functions. -/
noncomputable def reify : Stmt Γ Λ σ → Code
  | .halt => .halt
  | .goto f => .goto (unaryTable N (fun l => (N.label l).val) f)
  | .push k f q => .push (N.stack k).val (unaryTable N (fun x => (N.symbol k x).val) f) (reify q)
  | .peek k f q => .peek (N.stack k).val (readTable N k f) (reify q)
  | .pop k f q => .pop (N.stack k).val (readTable N k f) (reify q)
  | .load f q => .load (unaryTable N (fun x => (N.state x).val) f) (reify q)
  | .branch f a b => .branch (unaryTable N (fun b => if b then 1 else 0) f) (reify a) (reify b)

theorem reify_valid (q : Stmt Γ Λ σ) :
    valid N.stackCount N.states N.symbols N.labels (reify N q) = true := by
  induction q with
  | halt => rfl
  | goto f =>
    simpa [reify, valid] using unary_table_valid N (fun l => (N.label l).val) f N.labels (fun l => (N.label l).isLt)
  | push k f q ih =>
    have ht := unary_table_valid N (fun x => (N.symbol k x).val) f N.symbols
      (fun x => Nat.lt_of_lt_of_le (N.symbol k x).isLt (N.symbol_bound k))
    simp [reify, valid, (N.stack k).isLt, ht, ih]
  | peek k f q ih => simp [reify, valid, (N.stack k).isLt, read_table_valid N k f, ih]
  | pop k f q ih => simp [reify, valid, (N.stack k).isLt, read_table_valid N k f, ih]
  | load f q ih =>
    have ht := unary_table_valid N (fun x => (N.state x).val) f N.states (fun x => (N.state x).isLt)
    simp [reify, valid, ht, ih]
  | branch f a b iha ihb =>
    have ht := unary_table_valid N (fun b => if b then 1 else 0) f 2 (by intro b; cases b <;> decide)
    simp [reify, valid, ht, iha, ihb]

/-- Pointwise relation between heterogeneous stacks and numeric stacks. -/
def StackRel (S : ∀ k, List (Γ k)) (T : Nat → List Nat) : Prop :=
  ∀ k, T (N.stack k).val = (S k).map (fun x => (N.symbol k x).val)

def CfgRel (c : Cfg Γ Λ σ) (d : Cfg (fun _ : Nat => Nat) Nat Nat) : Prop :=
  d.l = c.l.map (fun l => (N.label l).val) ∧
  d.var = (N.state c.var).val ∧ StackRel N c.stk d.stk

theorem stackCode_injective : Function.Injective (fun k => (N.stack k).val) := by
  intro a b h
  exact N.stack.injective (Fin.ext h)

theorem stackRel_update [DecidableEq K] (S : ∀ k, List (Γ k)) (T : Nat → List Nat)
    (hr : StackRel N S T) (k : K) (xs : List (Γ k)) :
    StackRel N (Function.update S k xs)
      (Function.update T (N.stack k).val (xs.map fun x => (N.symbol k x).val)) := by
  intro j
  by_cases hj : j = k
  · subst j
    simp
  · have hn : (N.stack j).val ≠ (N.stack k).val := by
      intro h
      exact hj (stackCode_injective N h)
    simpa [Function.update_of_ne hj, Function.update_of_ne hn] using hr j

/-- Reified numeric statements execute exactly the same whole TM2 block
under the finite numberings. -/
theorem reify_stepAux [DecidableEq K] (q : Stmt Γ Λ σ) (v : σ)
    (S : ∀ k, List (Γ k)) (T : Nat → List Nat) (hr : StackRel N S T) :
    CfgRel N (stepAux q v S) (stepAux (interpret (reify N q)) (N.state v).val T) := by
  induction q generalizing v S T with
  | halt =>
    simp [reify, interpret, stepAux, CfgRel, hr]
  | goto f =>
    simp [reify, interpret, stepAux, CfgRel, unaryTable_lookup, hr]
  | push k f q ih =>
    have hnext := stackRel_update N S T hr k (f v :: S k)
    have hh : StackRel N (Function.update S k (f v :: S k))
        (Function.update T (N.stack k).val ((N.symbol k (f v)).val :: T (N.stack k).val)) := by
      simpa [hr k] using hnext
    have hi := ih v (Function.update S k (f v :: S k))
      (Function.update T (N.stack k).val ((N.symbol k (f v)).val :: T (N.stack k).val)) hh
    simpa [reify, interpret, stepAux, unaryTable_lookup] using hi
  | peek k f q ih =>
    have hhead : (T (N.stack k).val).head? = ((S k).head?).map (fun x => (N.symbol k x).val) := by
      rw [hr k]
      cases S k <;> rfl
    have hlookup : lookup₂ (readTable N k f) (N.state v).val
        (symbolIndex (T (N.stack k).val).head?) = some (N.state (f v (S k).head?)).val := by
      rw [hhead]
      exact readTable_lookup N k f v (S k).head?
    have hi := ih (f v (S k).head?) S T hr
    simpa [reify, interpret, stepAux, hlookup] using hi
  | pop k f q ih =>
    have hhead : (T (N.stack k).val).head? = ((S k).head?).map (fun x => (N.symbol k x).val) := by
      rw [hr k]
      cases S k <;> rfl
    have hlookup : lookup₂ (readTable N k f) (N.state v).val
        (symbolIndex (T (N.stack k).val).head?) = some (N.state (f v (S k).head?)).val := by
      rw [hhead]
      exact readTable_lookup N k f v (S k).head?
    have hnext := stackRel_update N S T hr k (S k).tail
    have hh : StackRel N (Function.update S k (S k).tail)
        (Function.update T (N.stack k).val (T (N.stack k).val).tail) := by
      have htail : ((S k).tail.map fun x => (N.symbol k x).val) =
          ((S k).map fun x => (N.symbol k x).val).tail := by cases S k <;> rfl
      simpa [hr k, htail] using hnext
    have hi := ih (f v (S k).head?) (Function.update S k (S k).tail)
      (Function.update T (N.stack k).val (T (N.stack k).val).tail) hh
    simpa [reify, interpret, stepAux, hlookup] using hi
  | load f q ih =>
    have hi := ih (f v) S T hr
    simpa [reify, interpret, stepAux, unaryTable_lookup] using hi
  | branch f a b iha ihb =>
    cases hf : f v with
    | false =>
      have hi := ihb v S T hr
      simpa [reify, interpret, stepAux, unaryTable_lookup, hf] using hi
    | true =>
      have hi := iha v S T hr
      simpa [reify, interpret, stepAux, unaryTable_lookup, hf] using hi

/-- Enumerate every label in the same numbering used by statement tables. -/
noncomputable def reifyProgram (P : Λ → Stmt Γ Λ σ) : List Code :=
  List.ofFn fun i : Fin N.labels => reify N (P (N.label.symm i))

@[simp] theorem reifyProgram_length (P : Λ → Stmt Γ Λ σ) :
    (reifyProgram N P).length = N.labels := by simp [reifyProgram]

theorem reifyProgram_lookup (P : Λ → Stmt Γ Λ σ) (l : Λ) :
    (reifyProgram N P)[(N.label l).val]? = some (reify N (P l)) := by
  simp [reifyProgram]

theorem reifyProgram_valid (P : Λ → Stmt Γ Λ σ) :
    Shared.Codes.TM2Program.programValid (reifyProgram N P) N.stackCount N.states N.symbols = true := by
  simp only [Shared.Codes.TM2Program.programValid, reifyProgram_length]
  apply List.all_eq_true.mpr
  intro q hq
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hq
  subst q
  exact reify_valid N (P (N.label.symm i))

/-- Pointwise option relation, with terminality matched on both sides. -/
def OptionCfgRel : Option (Cfg Γ Λ σ) → Option (Cfg (fun _ : Nat => Nat) Nat Nat) → Prop
  | none, none => True
  | some c, some d => CfgRel N c d
  | _, _ => False

theorem reifyProgram_step [DecidableEq K] (P : Λ → Stmt Γ Λ σ)
    (c : Cfg Γ Λ σ) (d : Cfg (fun _ : Nat => Nat) Nat Nat) (hr : CfgRel N c d) :
    OptionCfgRel N (Turing.TM2.step P c)
      (Turing.TM2.step (Shared.Codes.TM2Program.semanticProgram (reifyProgram N P)) d) := by
  rcases c with ⟨cl, cv, cS⟩
  rcases d with ⟨dl, dv, dS⟩
  rcases hr with ⟨hl, hv, hs⟩
  cases cl with
  | none =>
    simp only [Option.map_none] at hl
    subst dl
    trivial
  | some l =>
    simp only [Option.map_some] at hl
    subst dl
    change dv = (N.state cv).val at hv
    change StackRel N cS dS at hs
    subst dv
    have hi := reify_stepAux N (P l) cv cS dS hs
    have hp : Shared.Codes.TM2Program.semanticProgram (reifyProgram N P) (N.label l).val =
        interpret (reify N (P l)) := by
      unfold Shared.Codes.TM2Program.semanticProgram
      rw [reifyProgram_lookup N P l]
      rfl
    change CfgRel N (stepAux (P l) cv cS)
      (stepAux (Shared.Codes.TM2Program.semanticProgram (reifyProgram N P) (N.label l).val)
        (N.state cv).val dS)
    rw [hp]
    exact hi

/-- Finite alphabets supply numberings; choosing these numberings is a
mathematical existence step, not an executable reification of Lean functions. -/
noncomputable def numberingOfFinite (tm : Turing.FinTM2)
    (h : ∀ k, Finite (tm.Γ k)) : Numbering tm.Γ tm.Λ tm.σ := by
  letI : Fintype tm.K := tm.kFin
  letI : Fintype tm.Λ := tm.ΛFin
  letI : Fintype tm.σ := tm.σFin
  letI : ∀ k, Fintype (tm.Γ k) := fun k => @Fintype.ofFinite _ (h k)
  exact {
    stackCount := Fintype.card tm.K
    states := Fintype.card tm.σ
    labels := Fintype.card tm.Λ
    symbols := Finset.univ.sup (fun k : tm.K => Fintype.card (tm.Γ k))
    stack := Fintype.equivFin tm.K
    state := Fintype.equivFin tm.σ
    label := Fintype.equivFin tm.Λ
    symbolCount := fun k => Fintype.card (tm.Γ k)
    symbol := fun k => Fintype.equivFin (tm.Γ k)
    symbol_bound := fun k => Finset.le_sup (f := fun j : tm.K => Fintype.card (tm.Γ j)) (Finset.mem_univ k)
  }

open Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2Symbols

/-- Encode each finite stack using its own alphabet numbering. -/
def encodeStacks (S : ∀ k, List (Γ k)) : Stacks :=
  List.ofFn fun i : Fin N.stackCount =>
    let k := N.stack.symm i
    (S k).map fun x => (N.symbol k x).val

theorem encodeStacks_rel (S : ∀ k, List (Γ k)) :
    StackRel N S (stackFn (encodeStacks N S)) := by
  intro k
  simp [stackFn, encodeStacks]
  rw [N.stack.symm_apply_apply]

theorem encodeStacks_valid (S : ∀ k, List (Γ k)) :
    stacksValid N.stackCount N.symbols (encodeStacks N S) := by
  constructor
  · simp [encodeStacks]
  · intro xs hxs x hx
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hxs
    subst xs
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact Nat.lt_of_lt_of_le (N.symbol (N.stack.symm i) y).isLt (N.symbol_bound (N.stack.symm i))

def encodeConfig (c : Cfg Γ Λ σ) : Result :=
  ⟨c.l.map (fun l => (N.label l).val), (N.state c.var).val, encodeStacks N c.stk⟩

theorem encodeConfig_rel (c : Cfg Γ Λ σ) : CfgRel N c (erase (encodeConfig N c)) := by
  exact ⟨rfl, rfl, encodeStacks_rel N c.stk⟩

theorem encodeConfig_valid (P : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) :
    resultValid N.stackCount N.states N.symbols (reifyProgram N P).length (encodeConfig N c) := by
  refine ⟨(N.state c.var).isLt, encodeStacks_valid N c.stk, ?_⟩
  intro l hl
  cases hc : c.l with
  | none => simp [encodeConfig, hc] at hl
  | some label =>
    have heq : (N.label label).val = l := by simpa [encodeConfig, hc] using hl
    subst l
    simpa using (N.label label).isLt

/-- Reification preserves every finite exact run, counting the same whole
statement-block steps, including absent steps after halting. -/
theorem reifyProgram_steps [DecidableEq K] (P : Λ → Stmt Γ Λ σ) (n : Nat)
    (c : Cfg Γ Λ σ) (d : Cfg (fun _ : Nat => Nat) Nat Nat) (hr : CfgRel N c d) :
    OptionCfgRel N (runSteps (Turing.TM2.step P) n c)
      (runSteps (Turing.TM2.step (semanticProgram (reifyProgram N P))) n d) := by
  induction n generalizing c d with
  | zero => exact hr
  | succ n ih =>
    rw [runSteps_front, runSteps_front]
    have hstep := reifyProgram_step N P c d hr
    cases hc : Turing.TM2.step P c with
    | none =>
      cases hd : Turing.TM2.step (semanticProgram (reifyProgram N P)) d with
      | none => trivial
      | some d' => simp [hc, hd, OptionCfgRel] at hstep
    | some c' =>
      cases hd : Turing.TM2.step (semanticProgram (reifyProgram N P)) d with
      | none => simp [hc, hd, OptionCfgRel] at hstep
      | some d' =>
        have hrel : CfgRel N c' d' := by simpa [hc, hd, OptionCfgRel] using hstep
        exact ih c' d' hrel

/-- A halted original configuration reached within the block clock has a
matching successful result in the validated finite numeric runner. -/
theorem reified_halt_within [DecidableEq K] (P : Λ → Stmt Γ Λ σ)
    (c target : Cfg Γ Λ σ) (fuel n : Nat) (hn : n ≤ fuel)
    (hreach : runSteps (Turing.TM2.step P) n c = some target) (hhalt : target.l = none) :
    ∃ r, run (reifyProgram N P) fuel (encodeConfig N c) = .halted r ∧ CfgRel N target (erase r) := by
  let p := reifyProgram N P
  let start := encodeConfig N c
  have hsteps := reifyProgram_steps N P n c (erase start) (encodeConfig_rel N c)
  rw [hreach] at hsteps
  cases hnstep : runSteps (Turing.TM2.step (semanticProgram p)) n (erase start) with
  | none => simp [p, hnstep, OptionCfgRel] at hsteps
  | some d =>
    have hdrel : CfgRel N target d := by simpa [p, hnstep, OptionCfgRel] using hsteps
    have hdhalt : d.l = none := by simpa [CfgRel, hhalt] using hdrel.1
    have hp : programValid p N.stackCount N.states N.symbols = true := reifyProgram_valid N P
    have hstart : resultValid N.stackCount N.states N.symbols p.length start := encodeConfig_valid N P c
    have heq := (validated_halt_iff p N.stackCount N.states N.symbols fuel hp start hstart d hdhalt).2
      ⟨n, hn, hnstep⟩
    obtain ⟨r, hr, herase⟩ := heq
    exact ⟨r, hr, by simpa [herase] using hdrel⟩

set_option backward.isDefEq.respectTransparency false in
/-- A timed mathlib TM2 output has a matching halted numeric execution with
the same block clock, after finite alphabet numberings are chosen. -/
theorem finiteTM2_output_reified (tm : Turing.FinTM2) (finiteΓ : ∀ k, Finite (tm.Γ k))
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁)) (fuel : Nat)
    (hout : Turing.TM2OutputsInTime tm input (some output) fuel) :
    ∃ r, run (reifyProgram (numberingOfFinite tm finiteΓ) tm.m) fuel
        (encodeConfig (numberingOfFinite tm finiteΓ) (Turing.initList tm input)) = .halted r ∧
      CfgRel (numberingOfFinite tm finiteΓ) (Turing.haltList tm output) (erase r) := by
  let : DecidableEq tm.K := tm.kDecidableEq
  let N := numberingOfFinite tm finiteΓ
  have hreach : runSteps (Turing.TM2.step tm.m) hout.steps (Turing.initList tm input) =
      some (Turing.haltList tm output) := by
    rw [runSteps_iterate]
    exact hout.evals_in_steps
  exact reified_halt_within N tm.m (Turing.initList tm input) (Turing.haltList tm output)
    fuel hout.steps hout.steps_le_m hreach rfl

/-- A finite-alphabet polynomial-time witness supplies one valid numeric
program for every input, with the original statement-block polynomial clock. -/
theorem finitePolyWitness_reified {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : Turing.TM2ComputableInPolyTime ea eb f) (finiteΓ : ∀ k, Finite (h.tm.Γ k)) :
    ∃ (N : Numbering h.tm.Γ h.tm.Λ h.tm.σ) (p : List Code),
      p = reifyProgram N h.tm.m ∧ programValid p N.stackCount N.states N.symbols = true ∧
      ∀ a, ∃ r, run p (h.time.eval (ea a).length)
          (encodeConfig N (Turing.initList h.tm ((ea a).map h.inputAlphabet.invFun))) = .halted r ∧
        CfgRel N (Turing.haltList h.tm ((eb (f a)).map h.outputAlphabet.invFun)) (erase r) := by
  let N := numberingOfFinite h.tm finiteΓ
  refine ⟨N, reifyProgram N h.tm.m, rfl, reifyProgram_valid N h.tm.m, ?_⟩
  intro a
  exact finiteTM2_output_reified h.tm finiteΓ ((ea a).map h.inputAlphabet.invFun)
    ((eb (f a)).map h.outputAlphabet.invFun) (h.time.eval (ea a).length) (h.outputsFun a)

/-- Canonical polynomial-time functions have a finite numeric program code
whose bounded block execution represents the complete mathlib halt result.
The existence proof may choose numberings and tables classically; executable
decoding and bit-cost simulation are separate obligations. -/
theorem canonicalPoly_numeric {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f : α → β) (hf : ComplexityTheory.IsPolyTime f) :
    ∃ (h : Turing.TM2ComputableInPolyTime (BitstringEncoding.bitEncode (α := α))
        (BitstringEncoding.bitEncode (α := β)) f)
      (N : Numbering h.tm.Γ h.tm.Λ h.tm.σ) (p : List Code) (e : Nat),
      decodeProgram e = some p ∧ p = reifyProgram N h.tm.m ∧
      programValid p N.stackCount N.states N.symbols = true ∧
      ∀ a, ∃ r, run p (h.time.eval (BitstringEncoding.bitEncode a).length)
          (encodeConfig N (Turing.initList h.tm
            ((BitstringEncoding.bitEncode a).map h.inputAlphabet.invFun))) = .halted r ∧
        CfgRel N (Turing.haltList h.tm
          ((BitstringEncoding.bitEncode (f a)).map h.outputAlphabet.invFun)) (erase r) := by
  obtain ⟨h, hfinite⟩ := Shared.ComplexityBridge.TM2Symbols.polyTime_finite_witness f hf
  obtain ⟨N, p, hp, hv, hr⟩ := finitePolyWitness_reified h hfinite
  exact ⟨h, N, p, Encodable.encode p, decodeProgram_coverage p, hp, hv, hr⟩

end Shared.ComplexityBridge.TM2Reification
