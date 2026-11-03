import Shared.ComplexityBridge.TM2CNFValidate

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2CNFValidateTotal
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Source := Shared.ComplexityBridge.TM2CNFValidate.machine
abbrev Key := Shared.ComplexityBridge.TM2CNFValidate.Key
abbrev SourceLabel := Shared.ComplexityBridge.TM2CNFValidate.Label
abbrev SourceState := Shared.ComplexityBridge.TM2CNFValidate.State
abbrev Label := SourceLabel ⊕ Fin 8
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

def keyOf (i : Fin 7) : Key :=
  match i.val with | 0 => .stream | 1 => .clause | 2 => .outerScratch | 3 => .litInput | 4 => .litScratch | 5 => .litName | _ => .litAccum
def keyIndex : Key → Fin 7
  | .stream => 0 | .clause => 1 | .outerScratch => 2 | .litInput => 3 | .litScratch => 4 | .litName => 5 | .litAccum => 6
@[simp] theorem keyOf_index (k : Key) : keyOf (keyIndex k) = k := by cases k <;> rfl
@[simp] theorem index_keyOf (i : Fin 7) : keyIndex (keyOf i) = i := by fin_cases i <;> rfl

def stage (i : Fin 7) : Fin 8 := ⟨i.val,by omega⟩
def next (i : Fin 7) : Fin 8 := ⟨i.val+1,by omega⟩
def done : Fin 8 := ⟨7,by decide⟩

def cleanProgram (i : Fin 8) : Stmt (fun _ : Key => Bool) Label State :=
  if h : i.val < 7 then
    let j : Fin 7 := ⟨i.val,h⟩
    .pop (keyOf j) (fun v x => .inr ((cleanState v).1,x))
      (.branch (fun v => (cleanState v).2.isSome) (.goto (fun _ => .inr i)) (.goto (fun _ => .inr (next j))))
  else .push .stream (fun v => (cleanState v).1) (.load (fun _ => .inl Source.initialState) .halt)

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl (.inl .good) => .load (fun _ => .inr (true,none)) (.goto (fun _ => .inr 0))
  | .inl (.inl .bad) => .load (fun _ => .inr (false,none)) (.goto (fun _ => .inr 0))
  | .inl l => lift (Shared.ComplexityBridge.TM2CNFValidate.program l)
  | .inr i => cleanProgram i

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .stream
  k₁ := .stream
  Γ := fun _ => Bool
  Λ := Label
  main := .inl (.inl .start)
  σ := State
  initialState := .inl Source.initialState
  m := program

def terminal (q : Source.Cfg) : Prop := q.l = some (.inl .good) ∨ q.l = some (.inl .bad)
noncomputable instance : DecidablePred terminal := fun _ => Classical.propDecidable _
theorem stable (q : Source.Cfg) (h : terminal q) : Source.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some (Sum.inl Shared.ComplexityBridge.TM2CNFValidate.Phase.good) ∨ l = some (Sum.inl Shared.ComplexityBridge.TM2CNFValidate.Phase.bad) at h
    rcases h with h | h <;> subst l <;> rfl

theorem source_step (q : Source.Cfg) (h : ¬ terminal q) :
    machine.step (embed q) = (Source.step q).map embed := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | inl p => cases p with
        | good => exact False.elim (h (Or.inl rfl))
        | bad => exact False.elim (h (Or.inr rfl))
        | start | clear =>
          change some (stepAux (lift (Shared.ComplexityBridge.TM2CNFValidate.program _)) (.inl v) S) = _
          rw [lift_aux]; rfl
      | inr l =>
        change some (stepAux (lift (Shared.ComplexityBridge.TM2CNFValidate.program _)) (.inl v) S) = _
        rw [lift_aux]; rfl

def cleanCfg (i : Fin 8) (answer : Bool) (flag : Option Bool) (S : Key → List Bool) : machine.Cfg :=
  ⟨some (.inr i),.inr (answer,flag),S⟩

theorem dispatch (q : Source.Cfg) (answer : Bool)
    (h : q.l = some (.inl (if answer then .good else .bad))) :
    machine.step (embed q) = some (cleanCfg 0 answer none q.stk) := by
  cases q with
  | mk l v S => cases answer <;> simp only [Bool.false_eq_true,if_false,if_true] at h <;> subst l <;> rfl

theorem clean_cons (i : Fin 7) (answer : Bool) (flag : Option Bool) (S : Key → List Bool) (b : Bool) (xs : List Bool) :
    machine.step (cleanCfg (stage i) answer flag (Function.update S (keyOf i) (b::xs))) =
      some (cleanCfg (stage i) answer (some b) (Function.update S (keyOf i) xs)) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cleanCfg,program,cleanProgram,stage,dif_pos i.isLt,
    stepAux,cleanState,Function.update_self,List.head?_cons,Option.isSome_some,List.tail_cons,Bool.cond_true]
  congr 1; congr 1
  exact Function.update_idem _ _ _

theorem clean_nil (i : Fin 7) (answer : Bool) (flag : Option Bool) (S : Key → List Bool) :
    machine.step (cleanCfg (stage i) answer flag (Function.update S (keyOf i) [])) =
      some (cleanCfg (next i) answer none (Function.update S (keyOf i) [])) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cleanCfg,program,cleanProgram,stage,dif_pos i.isLt,
    stepAux,cleanState,Function.update_self,List.head?_nil,Option.isSome_none,List.tail_nil,Bool.cond_false]
  congr 1; congr 1
  exact Function.update_idem _ _ _

theorem sweep_one (i : Fin 7) (answer : Bool) (flag : Option Bool) (S : Key → List Bool) (xs : List Bool) :
    runSteps machine.step (xs.length+1) (cleanCfg (stage i) answer flag (Function.update S (keyOf i) xs)) =
      some (cleanCfg (next i) answer none (Function.update S (keyOf i) [])) := by
  induction xs generalizing flag with
  | nil => exact clean_nil i answer flag S
  | cons b xs ih =>
    rw [List.length_cons,show xs.length+1+1 = (xs.length+1)+1 by omega,runSteps_front,clean_cons]
    exact ih (some b)

theorem sweep_suffix (answer : Bool) (bound n : Nat) :
    ∀ (a : Nat) (ha : a+n = 7) (S : Key → List Bool) (flag : Option Bool),
      (∀ k, (keyIndex k).val < a → S k = []) → (∀ k, (S k).length ≤ bound) →
      ∃ t ≤ n*(bound+1), ∃ f,
        runSteps machine.step t (cleanCfg ⟨a,by omega⟩ answer flag S) =
          some (cleanCfg done answer f (fun _ => [])) := by
  induction n with
  | zero =>
    intro a ha S flag hempty hbound
    have ae : a = 7 := by omega
    have hS : S = fun _ => [] := by
      funext k; apply hempty; have hk := (keyIndex k).isLt; omega
    subst S
    have hl : (⟨a,by omega⟩ : Fin 8) = done := by apply Fin.ext; simp [done,ae]
    refine ⟨0,by simp,flag,?_⟩
    rw [hl]; rfl
  | succ n ih =>
    intro a ha S flag hempty hbound
    have halt : a < 7 := by omega
    let i : Fin 7 := ⟨a,halt⟩
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
    have hstage : stage i = (⟨a,by omega⟩ : Fin 8) := by apply Fin.ext; rfl
    have hnext : next i = (⟨a+1,by omega⟩ : Fin 8) := by apply Fin.ext; rfl
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
  have hn : ¬done.val < 7 := by simp [done]
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cleanCfg,program,cleanProgram,dif_neg hn,stepAux,cleanState]
  congr 1
  change Cfg.mk none (.inl Source.initialState : State) (Function.update (fun _ : Key => ([] : List Bool)) Shared.ComplexityBridge.TM2CNFValidate.Key.stream [answer]) = _
  congr 1; funext k; cases k <;> simp [Function.update,Turing.haltList,machine] <;> rfl

theorem sweep_all (answer : Bool) (S : Key → List Bool) (bound : Nat)
    (hbound : ∀ k, (S k).length ≤ bound) :
    ∃ t ≤ 7*(bound+1)+1, runSteps machine.step t (cleanCfg 0 answer none S) =
      some (Turing.haltList machine [answer]) := by
  obtain ⟨t,ht,flag,hr⟩ := sweep_suffix answer bound 7 0 (by omega) S none (by intro k hk; omega) hbound
  refine ⟨t+1,by omega,?_⟩
  change runSteps machine.step (t+1) (cleanCfg ⟨0,by omega⟩ answer none S) = _
  rw [runSteps_add,hr]
  exact finish answer flag


theorem initial_eq (input : List Bool) : Turing.initList machine input = embed (Turing.initList Source input) := by
  rfl

noncomputable def timePolynomial : Polynomial Nat :=
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source
  let P := Polynomial.X*Shared.ComplexityBridge.TM2CNFValidate.iterationPolynomial+Polynomial.C 1
  P+Polynomial.C 1+Polynomial.C 7*(Polynomial.X+P*Polynomial.C D+Polynomial.C 1)+Polynomial.C 1

theorem timePolynomial_eval (n : Nat) :
    timePolynomial.eval n = (n*Shared.ComplexityBridge.TM2CNFValidate.iterationPolynomial.eval n+1)+1+
      7*(n+(n*Shared.ComplexityBridge.TM2CNFValidate.iterationPolynomial.eval n+1)*
        Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source+1)+1 := by
  simp [timePolynomial]

/-- A finite TM2 validates every input, empties every auxiliary stack, and
halts with the exact Boolean answer within the explicit polynomial. -/
theorem total_run (input : List Bool) :
    ∃ t ≤ timePolynomial.eval input.length,
      runSteps machine.step t (Turing.initList machine input) =
        some (Turing.haltList machine [Shared.ComplexityBridge.TM2CNFValidate.validate input]) := by
  let P := input.length*Shared.ComplexityBridge.TM2CNFValidate.iterationPolynomial.eval input.length+1
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source
  let answer := Shared.ComplexityBridge.TM2CNFValidate.validate input
  obtain ⟨n,hn,q,hr,hq⟩ := Shared.ComplexityBridge.TM2CNFValidate.validation_run input none
  rw [← Shared.ComplexityBridge.TM2CNFValidate.initial_eq] at hr
  change n ≤ P at hn
  change q.l = some (.inl (if answer then .good else .bad)) at hq
  have hterm : terminal q := by
    unfold terminal
    cases he : answer with
    | false => right; simpa [he] using hq
    | true => left; simpa [he] using hq
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Source.step machine.step embed terminal stable source_step n (Turing.initList Source input) q hterm hr
  have hstack : ∀ k : Key, (q.stk k).length ≤ input.length+P*D := by
    intro k
    have hs := Shared.ComplexityBridge.TM2GenericStackBound.run_from_input_length Source input n q hr k
    have hm := Nat.mul_le_mul_right D hn
    change (q.stk k).length ≤ input.length+n*D at hs
    omega
  obtain ⟨b,hb,hbr⟩ := sweep_all answer q.stk (input.length+P*D) hstack
  refine ⟨a+1+b,?_,?_⟩
  · rw [timePolynomial_eval]
    change a+1+b ≤ P+1+7*(input.length+P*D+1)+1
    omega
  · change runSteps machine.step (a+1+b) (Turing.initList machine input) = some (Turing.haltList machine [answer])
    rw [initial_eq,show a+1+b = a+(1+b) by omega,runSteps_add,har]
    change runSteps machine.step (1+b) (embed q) = _
    rw [runSteps_add]
    change (machine.step (embed q)).bind _ = _
    rw [dispatch q answer hq]
    exact hbr

/-- The machine's output uses the public Boolean encoding, with raw input. -/
noncomputable def rawTimeMachine : Turing.TM2ComputableInPolyTime
    (id : List Bool → List Bool) (BitstringEncoding.bitEncode : Bool → List Bool)
    Shared.ComplexityBridge.TM2CNFValidate.validate where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun input := by
    let t := Classical.choose (total_run input)
    have ht := (Classical.choose_spec (total_run input)).1
    have hr := (Classical.choose_spec (total_run input)).2
    refine ⟨⟨t,?_⟩,?_⟩
    · rw [runSteps_iterate] at hr
      change (fun o => o.bind machine.step)^[t] (some (Turing.initList machine (input.map id))) =
        some (Turing.haltList machine ((BitstringEncoding.bitEncode (Shared.ComplexityBridge.TM2CNFValidate.validate input)).map id))
      rw [List.map_id,List.map_id]
      change (fun o => o.bind machine.step)^[t] (some (Turing.initList machine input)) =
        some (Turing.haltList machine [Shared.ComplexityBridge.TM2CNFValidate.validate input])
      simpa [t] using hr
    · simpa using ht

/-- Canonical polynomial time, including the cost of decoding its input. -/
theorem validate_isPolyTime : ComplexityTheory.IsPolyTime Shared.ComplexityBridge.TM2CNFValidate.validate := by
  exact Shared.ComplexityBridge.TM2ComposeEncoded.compose
    (BitstringEncoding.bitEncode : List Bool → List Bool) (id : List Bool → List Bool)
    (BitstringEncoding.bitEncode : Bool → List Bool) (id : List Bool → List Bool)
    Shared.ComplexityBridge.TM2CNFValidate.validate Shared.ComplexityBridge.TM2ListCodec.Decode.timeMachine rawTimeMachine

/-- Valid-CNF parsing, not SAT or UNSAT, is in canonical P on all inputs. -/
theorem parseSuccess_isPolyTime : ComplexityTheory.IsPolyTime
    (fun input => (Shared.ComplexityBridge.CNF.parse input).isSome) := by
  have he : Shared.ComplexityBridge.TM2CNFValidate.validate =
      (fun input => (Shared.ComplexityBridge.CNF.parse input).isSome) := by
    funext input; exact Shared.ComplexityBridge.TM2CNFValidate.validate_correct input
  rw [← he]
  exact validate_isPolyTime

namespace Fixtures

-- Empty formula and a formula with one empty clause are both syntactically valid.
example : (runSteps machine.step 10 (Turing.initList machine [])).map
    (fun q => (q.l.isNone,q.stk .stream)) = some (true,[true]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .stream)) (runSteps machine.step 10 (Turing.initList machine [])) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 17 (Turing.initList machine [false])).map
    (fun q => (q.l.isNone,q.stk .stream)) = some (true,[true]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .stream)) (runSteps machine.step 17 (Turing.initList machine [false])) : Option (Bool × List Bool)) = _
  decide

-- The two fragments that flattened into a valid literal are rejected in place.
set_option maxRecDepth 4096 in
example : (runSteps machine.step 33 (Turing.initList machine
    Shared.ComplexityBridge.CNFOccurrences.Fixtures.crossedClauses)).map
    (fun q => (q.l.isNone,q.stk .stream)) = some (true,[false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .stream)) (runSteps machine.step 33 (Turing.initList machine
    Shared.ComplexityBridge.CNFOccurrences.Fixtures.crossedClauses)) : Option (Bool × List Bool)) = _
  decide

end Fixtures

end Shared.ComplexityBridge.TM2CNFValidateTotal
