import Shared.ComplexityBridge.TM2FormulaEval

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2FormulaOutput
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Source := Shared.ComplexityBridge.TM2FormulaEval.machine
abbrev Key := Shared.ComplexityBridge.TM2FormulaEval.Key
abbrev SourceLabel := Shared.ComplexityBridge.TM2FormulaEval.Label
abbrev SourceState := Shared.ComplexityBridge.TM2FormulaEval.State
abbrev Label := SourceLabel ⊕ Fin 14
abbrev State := SourceState ⊕ (Bool × Option Bool)
def sourceState : State → SourceState | .inl v => v | _ => Source.initialState
def cleanState : State → Bool × Option Bool | .inr v => v | _ => (false,none)
def embed (q : Source.Cfg) : Cfg (fun _ : Key => Bool) Label State := ⟨q.l.map Sum.inl,.inl q.var,q.stk⟩

def lift : Stmt (fun _ : Key => Bool) SourceLabel SourceState → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push j (fun v => f (sourceState v)) (lift q)
  | .peek j f q => .peek j (fun v h => .inl (f (sourceState v) h)) (lift q)
  | .pop j f q => .pop j (fun v h => .inl (f (sourceState v) h)) (lift q)
  | .load f q => .load (fun v => .inl (f (sourceState v))) (lift q)
  | .branch f q r => .branch (fun v => f (sourceState v)) (lift q) (lift r)
  | .goto f => .goto (fun v => .inl (f (sourceState v)))
  | .halt => .halt

theorem lift_aux (q : Source.Stmt) (v : SourceState) (S : Key → List Bool) :
    stepAux (lift q) (.inl v) S = embed (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih => exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih => exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [lift,stepAux,sourceState,h,ihq,ihr]

def keyOf (i : Fin 13) : Key :=
  match i.val with
  | 0 => .inl (.inl (.inl .vars)) | 1 => .inl (.inl (.inl .witness))
  | 2 => .inl (.inl (.inl .query)) | 3 => .inl (.inl (.inl .scratch))
  | 4 => .inl (.inl (.inl .left)) | 5 => .inl (.inl (.inl .right))
  | 6 => .inl (.inl (.inr .vars)) | 7 => .inl (.inl (.inr .witness))
  | 8 => .inl (.inl (.inr .scratch)) | 9 => .inl (.inr .stream)
  | 10 => .inl (.inr .scratch) | 11 => .inr .stream | _ => .inr .scratch

def keyIndex : Key → Fin 13
  | .inl (.inl (.inl .vars)) => 0 | .inl (.inl (.inl .witness)) => 1
  | .inl (.inl (.inl .query)) => 2 | .inl (.inl (.inl .scratch)) => 3
  | .inl (.inl (.inl .left)) => 4 | .inl (.inl (.inl .right)) => 5
  | .inl (.inl (.inr .vars)) => 6 | .inl (.inl (.inr .witness)) => 7
  | .inl (.inl (.inr .scratch)) => 8 | .inl (.inr .stream) => 9
  | .inl (.inr .scratch) => 10 | .inr .stream => 11 | .inr .scratch => 12
@[simp] theorem keyOf_index (k : Key) : keyOf (keyIndex k) = k := by
  cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k <;> rfl
@[simp] theorem index_keyOf (i : Fin 13) : keyIndex (keyOf i) = i := by fin_cases i <;> rfl

def stage (i : Fin 13) : Fin 14 := ⟨i.val,by omega⟩
def next (i : Fin 13) : Fin 14 := ⟨i.val+1,by omega⟩
def done : Fin 14 := ⟨13,by decide⟩

def cleanProgram (i : Fin 14) : Stmt (fun _ : Key => Bool) Label State :=
  if h : i.val < 13 then
    let j : Fin 13 := ⟨i.val,h⟩
    .pop (keyOf j) (fun v x => .inr ((cleanState v).1,x))
      (.branch (fun v => (cleanState v).2.isSome) (.goto (fun _ => .inr i)) (.goto (fun _ => .inr (next j))))
  else .push (.inr .stream) (fun v => (cleanState v).1) (.load (fun _ => .inl Source.initialState) .halt)

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl (.inl .yes) => .load (fun _ => .inr (true,none)) (.goto (fun _ => .inr 0))
  | .inl (.inl .no) => .load (fun _ => .inr (false,none)) (.goto (fun _ => .inr 0))
  | .inl (.inl .invalid) => .load (fun _ => .inr (false,none)) (.goto (fun _ => .inr 0))
  | .inl l => lift (Shared.ComplexityBridge.TM2FormulaEval.program l)
  | .inr i => cleanProgram i

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .inr .stream
  k₁ := .inr .stream
  Γ := fun _ => Bool
  Λ := Label
  main := .inl (.inl .start)
  σ := State
  initialState := .inl Source.initialState
  m := program

def terminal (q : Source.Cfg) : Prop := q.l = some (.inl .yes) ∨ q.l = some (.inl .no) ∨ q.l = some (.inl .invalid)
noncomputable instance : DecidablePred terminal := fun _ => Classical.propDecidable _
theorem stable (q : Source.Cfg) (h : terminal q) : Source.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some (.inl Shared.ComplexityBridge.TM2FormulaEval.Phase.yes) ∨
      l = some (.inl Shared.ComplexityBridge.TM2FormulaEval.Phase.no) ∨
      l = some (.inl Shared.ComplexityBridge.TM2FormulaEval.Phase.invalid) at h
    rcases h with h | h | h <;> subst l <;> rfl

theorem source_step (q : Source.Cfg) (h : ¬ terminal q) :
    machine.step (embed q) = (Source.step q).map embed := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | inl p => cases p with
        | yes => exact False.elim (h (Or.inl rfl))
        | no => exact False.elim (h (Or.inr (Or.inl rfl)))
        | invalid => exact False.elim (h (Or.inr (Or.inr rfl)))
        | start =>
          change some (stepAux (lift (Shared.ComplexityBridge.TM2FormulaEval.program _)) (.inl v) S) = _
          rw [lift_aux]; rfl
      | inr l =>
        change some (stepAux (lift (Shared.ComplexityBridge.TM2FormulaEval.program _)) (.inl v) S) = _
        rw [lift_aux]; rfl

def cleanCfg (i : Fin 14) (answer : Bool) (flag : Option Bool) (S : Key → List Bool) : machine.Cfg :=
  ⟨some (.inr i),.inr (answer,flag),S⟩

theorem dispatch (q : Source.Cfg) (r : Option Bool)
    (h : q.l = some (.inl (match r with | none => .invalid | some true => .yes | some false => .no))) :
    machine.step (embed q) = some (cleanCfg 0 (r.getD false) none q.stk) := by
  cases q with
  | mk l v S =>
    cases r with
    | none => change l = some (.inl .invalid) at h; subst l; rfl
    | some b => cases b <;> simp only at h ⊢ <;> subst l <;> rfl

theorem clean_cons (i : Fin 13) (answer : Bool) (flag : Option Bool) (S : Key → List Bool) (b : Bool) (xs : List Bool) :
    machine.step (cleanCfg (stage i) answer flag (Function.update S (keyOf i) (b::xs))) =
      some (cleanCfg (stage i) answer (some b) (Function.update S (keyOf i) xs)) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cleanCfg,program,cleanProgram,stage,dif_pos i.isLt,
    stepAux,cleanState,Function.update_self,List.head?_cons,Option.isSome_some,List.tail_cons,Bool.cond_true]
  congr 1; congr 1
  exact Function.update_idem _ _ _

theorem clean_nil (i : Fin 13) (answer : Bool) (flag : Option Bool) (S : Key → List Bool) :
    machine.step (cleanCfg (stage i) answer flag (Function.update S (keyOf i) [])) =
      some (cleanCfg (next i) answer none (Function.update S (keyOf i) [])) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cleanCfg,program,cleanProgram,stage,dif_pos i.isLt,
    stepAux,cleanState,Function.update_self,List.head?_nil,Option.isSome_none,List.tail_nil,Bool.cond_false]
  congr 1; congr 1
  exact Function.update_idem _ _ _

theorem sweep_one (i : Fin 13) (answer : Bool) (flag : Option Bool) (S : Key → List Bool) (xs : List Bool) :
    runSteps machine.step (xs.length+1) (cleanCfg (stage i) answer flag (Function.update S (keyOf i) xs)) =
      some (cleanCfg (next i) answer none (Function.update S (keyOf i) [])) := by
  induction xs generalizing flag with
  | nil => exact clean_nil i answer flag S
  | cons b xs ih =>
    rw [List.length_cons,show xs.length+1+1 = (xs.length+1)+1 by omega,runSteps_front,clean_cons]
    exact ih (some b)

theorem sweep_suffix (answer : Bool) (bound n : Nat) :
    ∀ (a : Nat) (ha : a+n = 13) (S : Key → List Bool) (flag : Option Bool),
      (∀ k, (keyIndex k).val < a → S k = []) → (∀ k, (S k).length ≤ bound) →
      ∃ t ≤ n*(bound+1), ∃ f,
        runSteps machine.step t (cleanCfg ⟨a,by omega⟩ answer flag S) =
          some (cleanCfg done answer f (fun _ => [])) := by
  induction n with
  | zero =>
    intro a ha S flag hempty hbound
    have ae : a = 13 := by omega
    have hS : S = fun _ => [] := by
      funext k; apply hempty; have hk := (keyIndex k).isLt; omega
    subst S
    have hl : (⟨a,by omega⟩ : Fin 14) = done := by apply Fin.ext; simp [done,ae]
    refine ⟨0,by simp,flag,?_⟩
    rw [hl]; rfl
  | succ n ih =>
    intro a ha S flag hempty hbound
    have halt : a < 13 := by omega
    let i : Fin 13 := ⟨a,halt⟩
    let S' := Function.update S (keyOf i) []
    have hempty' : ∀ k, (keyIndex k).val < a+1 → S' k = [] := by
      intro k hk
      by_cases heq : k = keyOf i
      · subst k; simp [S']
      · have hval : (keyIndex k).val ≠ a := by
          intro hv
          have hi : keyIndex k = i := Fin.ext hv
          apply heq
          calc
            k = keyOf (keyIndex k) := by simp
            _ = keyOf i := by rw [hi]
        have hlt : (keyIndex k).val < a := by omega
        simpa [S',Function.update_of_ne heq] using hempty k hlt
    have hbound' : ∀ k, (S' k).length ≤ bound := by
      intro k
      by_cases heq : k = keyOf i
      · subst k; simp [S']
      · simpa [S',Function.update_of_ne heq] using hbound k
    obtain ⟨t,ht,f,hrun⟩ := ih (a+1) (by omega) S' none hempty' hbound'
    have hstage : stage i = (⟨a,by omega⟩ : Fin 14) := by apply Fin.ext; rfl
    have hnext : next i = (⟨a+1,by omega⟩ : Fin 14) := by apply Fin.ext; rfl
    have hone := sweep_one i answer flag S (S (keyOf i))
    rw [Function.update_eq_self,hstage,hnext] at hone
    have htbound : (S (keyOf i)).length+1+t ≤ (n+1)*(bound+1) := by
      have hi := hbound (keyOf i)
      rw [Nat.add_mul,Nat.one_mul]
      omega
    refine ⟨(S (keyOf i)).length+1+t,by simpa using htbound,f,?_⟩
    rw [runSteps_add,hone]
    exact hrun

theorem finish (answer : Bool) (flag : Option Bool) :
    machine.step (cleanCfg done answer flag (fun _ => [])) = some (Turing.haltList machine [answer]) := by
  have hn : ¬done.val < 13 := by simp [done]
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cleanCfg,program,cleanProgram,dif_neg hn,stepAux,cleanState]
  congr 1
  change Cfg.mk none (.inl Source.initialState : State) (Function.update (fun _ : Key => ([] : List Bool)) (Sum.inr Shared.ComplexityBridge.TM2FormulaEval.Extra.stream) [answer]) = _
  congr 1; funext k; cases k with
  | inl k => simp [Function.update,Turing.haltList,machine] <;> rfl
  | inr k => cases k <;> simp [Function.update,Turing.haltList,machine] <;> rfl

theorem sweep_all (answer : Bool) (S : Key → List Bool) (bound : Nat)
    (hbound : ∀ k, (S k).length ≤ bound) :
    ∃ t ≤ 13*(bound+1)+1, runSteps machine.step t (cleanCfg 0 answer none S) =
      some (Turing.haltList machine [answer]) := by
  obtain ⟨t,ht,flag,hr⟩ := sweep_suffix answer bound 13 0 (by omega) S none (by intro k hk; omega) hbound
  refine ⟨t+1,by omega,?_⟩
  change runSteps machine.step (t+1) (cleanCfg ⟨0,by omega⟩ answer none S) = _
  rw [runSteps_add,hr]
  exact finish answer flag



noncomputable def timePolynomial : Polynomial Nat :=
  let P := Shared.ComplexityBridge.TM2FormulaEval.timePolynomial
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source
  P+Polynomial.C 1+Polynomial.C 13*(Polynomial.X+P*Polynomial.C D+Polynomial.C 1)+Polynomial.C 1

theorem timePolynomial_eval (n : Nat) :
    timePolynomial.eval n = Shared.ComplexityBridge.TM2FormulaEval.timePolynomial.eval n+1+
      13*(n+Shared.ComplexityBridge.TM2FormulaEval.timePolynomial.eval n*
        Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source+1)+1 := by
  simp [timePolynomial]

/-- The loaded finite formula evaluator followed by a charged thirteen-stack
sweep halts with a Boolean output. Malformed formulas return false. -/
theorem loaded_run (vars : List (List Bool)) (witness input : List Bool) :
    let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
    let size := frame.length+witness.length+input.length
    let start := Shared.ComplexityBridge.TM2FormulaEval.cfg .start true none input frame witness
    ∃ t ≤ timePolynomial.eval size,
      runSteps machine.step t (embed start) =
        some (Turing.haltList machine [(Shared.ComplexityBridge.RawCNFEval.formula vars witness input).getD false]) := by
  let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
  let size := frame.length+witness.length+input.length
  let P := Shared.ComplexityBridge.TM2FormulaEval.timePolynomial.eval size
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source
  let start := Shared.ComplexityBridge.TM2FormulaEval.cfg .start true none input frame witness
  let result := Shared.ComplexityBridge.RawCNFEval.formula vars witness input
  obtain ⟨n,hn,q,hr,hq⟩ := Shared.ComplexityBridge.TM2FormulaEval.formula_progress vars witness input
  change n ≤ P at hn
  change runSteps Source.step n start = some q at hr
  change q.l = some (.inl (match result with | none => .invalid | some true => .yes | some false => .no)) at hq
  have hterminal : terminal q := by
    unfold terminal
    cases hr : result with
    | none => right; right; simpa [hr] using hq
    | some b => cases b with
      | false => right; left; simpa [hr] using hq
      | true => left; simpa [hr] using hq
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Source.step machine.step embed terminal stable source_step n start q hterminal hr
  have hstart : ∀ k : Key, (start.stk k).length ≤ size := by
    intro k
    cases k with
    | inl k => cases k with
      | inl k => cases k with
        | inl k => cases k <;> simp [start,Shared.ComplexityBridge.TM2FormulaEval.cfg,Shared.ComplexityBridge.TM2FormulaEval.stackVals,Shared.ComplexityBridge.TM2FormulaEval.istacks,Shared.ComplexityBridge.TM2ClauseEval.stackVals,Shared.ComplexityBridge.TM2ClauseEval.istacks,Shared.ComplexityBridge.TM2LiteralPreserve.combinedStacks,Shared.ComplexityBridge.TM2LiteralPreserve.extras,size] <;> omega
        | inr k => cases k <;> simp [start,Shared.ComplexityBridge.TM2FormulaEval.cfg,Shared.ComplexityBridge.TM2FormulaEval.stackVals,Shared.ComplexityBridge.TM2FormulaEval.istacks,Shared.ComplexityBridge.TM2ClauseEval.stackVals,Shared.ComplexityBridge.TM2ClauseEval.istacks,Shared.ComplexityBridge.TM2LiteralPreserve.combinedStacks,Shared.ComplexityBridge.TM2LiteralPreserve.extras,size] <;> omega
      | inr k => cases k <;> simp [start,Shared.ComplexityBridge.TM2FormulaEval.cfg,Shared.ComplexityBridge.TM2FormulaEval.stackVals,Shared.ComplexityBridge.TM2FormulaEval.istacks,Shared.ComplexityBridge.TM2ClauseEval.stackVals,Shared.ComplexityBridge.TM2ClauseEval.istacks,Shared.ComplexityBridge.TM2LiteralPreserve.combinedStacks,Shared.ComplexityBridge.TM2LiteralPreserve.extras,size] <;> omega
    | inr k => cases k <;> simp [start,Shared.ComplexityBridge.TM2FormulaEval.cfg,Shared.ComplexityBridge.TM2FormulaEval.stackVals,Shared.ComplexityBridge.TM2FormulaEval.istacks,Shared.ComplexityBridge.TM2ClauseEval.stackVals,Shared.ComplexityBridge.TM2ClauseEval.istacks,Shared.ComplexityBridge.TM2LiteralPreserve.combinedStacks,Shared.ComplexityBridge.TM2LiteralPreserve.extras,size] <;> omega
  have hstack : ∀ k : Key, (q.stk k).length ≤ size+P*D := by
    intro k
    have hh := Shared.ComplexityBridge.TM2GenericStackBound.run_length Source n start q hr k
    have hm := Nat.mul_le_mul_right D hn
    have hs := hstart k
    change (q.stk k).length ≤ (start.stk k).length+n*D at hh
    omega
  obtain ⟨c,hc,hcr⟩ := sweep_all (result.getD false) q.stk (size+P*D) hstack
  refine ⟨a+1+c,?_,?_⟩
  · rw [timePolynomial_eval]
    change a+1+c ≤ P+1+13*(size+P*D+1)+1
    omega
  · change runSteps machine.step (a+1+c) (embed start) = some (Turing.haltList machine [result.getD false])
    rw [show a+1+c = a+(1+c) by omega,runSteps_add,har]
    change runSteps machine.step (1+c) (embed q) = _
    rw [runSteps_add]
    change (machine.step (embed q)).bind _ = _
    rw [dispatch q result hq]
    exact hcr

/-- On valid formulas, the output is the public CNF evaluation under the
loaded occurrence assignment. -/
theorem loaded_run_correct (vars : List (List Bool)) (witness input : List Bool)
    (formula : Shared.ComplexityBridge.CNF.Formula) (h : Shared.ComplexityBridge.CNF.parse input = some formula) :
    let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
    let size := frame.length+witness.length+input.length
    let start := Shared.ComplexityBridge.TM2FormulaEval.cfg .start true none input frame witness
    ∃ t ≤ timePolynomial.eval size,
      runSteps machine.step t (embed start) = some (Turing.haltList machine
        [Shared.ComplexityBridge.CNF.evalFormula
          (Shared.ComplexityBridge.CNF.assignment (vars.map Computability.decodeNat) witness) formula]) := by
  simpa [Shared.ComplexityBridge.RawCNFEval.formula_eq,h] using loaded_run vars witness input

/-- Malformed formulas halt with false under the same charged bound. -/
theorem loaded_run_invalid (vars : List (List Bool)) (witness input : List Bool)
    (h : Shared.ComplexityBridge.CNF.parse input = none) :
    let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
    let size := frame.length+witness.length+input.length
    let start := Shared.ComplexityBridge.TM2FormulaEval.cfg .start true none input frame witness
    ∃ t ≤ timePolynomial.eval size,
      runSteps machine.step t (embed start) = some (Turing.haltList machine [false]) := by
  simpa [Shared.ComplexityBridge.RawCNFEval.formula_eq,h] using loaded_run vars witness input


/-- The finite occurrence projection supplies the loaded frame for the
canonical certificate relation on valid inputs. Projection and loading are
not included in this machine's bound. -/
theorem verifier_loaded_run (input witness : List Bool) (formula : Shared.ComplexityBridge.CNF.Formula)
    (h : Shared.ComplexityBridge.CNF.parse input = some formula) :
    ∃ vars : List (List Bool),
      Shared.ComplexityBridge.CNFOccurrences.project input = true::Shared.ComplexityBridge.TM2WitnessLookup.frames vars ∧
      ∃ t ≤ timePolynomial.eval ((Shared.ComplexityBridge.TM2WitnessLookup.frames vars).length+witness.length+input.length),
        runSteps machine.step t (embed (Shared.ComplexityBridge.TM2FormulaEval.cfg .start true none input
          (Shared.ComplexityBridge.TM2WitnessLookup.frames vars) witness)) =
          some (Turing.haltList machine [Shared.ComplexityBridge.CNFWitness.verify (input,witness)]) := by
  obtain ⟨vars,hvars,hproject⟩ := Shared.ComplexityBridge.CNFOccurrences.project_correct_of_parse input formula h
  obtain ⟨t,ht,hr⟩ := loaded_run_correct vars witness input formula h
  refine ⟨vars,hproject,t,ht,?_⟩
  simpa [Shared.ComplexityBridge.CNFWitness.verify,h,hvars] using hr


namespace Fixtures
example : (runSteps machine.step 16 (embed (Shared.ComplexityBridge.TM2FormulaEval.cfg .start true none [] [] []))).map
    (fun q => (q.l.isNone,q.stk (.inr .stream))) = some (true,[true]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr .stream)))
    (runSteps machine.step 16 (embed (Shared.ComplexityBridge.TM2FormulaEval.cfg .start true none [] [] []))) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 22 (embed (Shared.ComplexityBridge.TM2FormulaEval.cfg .start true none [false] [] []))).map
    (fun q => (q.l.isNone,q.stk (.inr .stream))) = some (true,[false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr .stream)))
    (runSteps machine.step 22 (embed (Shared.ComplexityBridge.TM2FormulaEval.cfg .start true none [false] [] []))) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 19 (embed (Shared.ComplexityBridge.TM2FormulaEval.cfg .start true none [true] [] []))).map
    (fun q => (q.l.isNone,q.stk (.inr .stream))) = some (true,[false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr .stream)))
    (runSteps machine.step 19 (embed (Shared.ComplexityBridge.TM2FormulaEval.cfg .start true none [true] [] []))) : Option (Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2FormulaOutput
