import Shared.ComplexityBridge.TM2WitnessLookup

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2WitnessOutput
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Source := Shared.ComplexityBridge.TM2WitnessLookup.machine
abbrev Key := Shared.ComplexityBridge.TM2WitnessLookup.Key
abbrev SourceLabel := Shared.ComplexityBridge.TM2WitnessLookup.Label
abbrev SourceState := Shared.ComplexityBridge.TM2WitnessLookup.State
abbrev Label := SourceLabel ⊕ Fin 7
abbrev State := SourceState ⊕ (Bool × Option Bool)
def sourceState : State → SourceState | .inl v => v | _ => (false,false,.inr (.inr none))
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

def keyOf (i : Fin 6) : Key :=
  match i.val with | 0 => .vars | 1 => .witness | 2 => .query | 3 => .scratch | 4 => .left | _ => .right
def keyIndex : Key → Fin 6
  | .vars => 0 | .witness => 1 | .query => 2 | .scratch => 3 | .left => 4 | .right => 5
@[simp] theorem keyOf_index (k : Key) : keyOf (keyIndex k) = k := by cases k <;> rfl
@[simp] theorem index_keyOf (i : Fin 6) : keyIndex (keyOf i) = i := by fin_cases i <;> rfl

def stage (i : Fin 6) : Fin 7 := ⟨i.val,by omega⟩
def next (i : Fin 6) : Fin 7 := ⟨i.val+1,by omega⟩
def done : Fin 7 := ⟨6,by decide⟩

def cleanProgram (i : Fin 7) : Stmt (fun _ : Key => Bool) Label State :=
  if h : i.val < 6 then
    let j : Fin 6 := ⟨i.val,h⟩
    .pop (keyOf j) (fun v x => .inr ((cleanState v).1,x))
      (.branch (fun v => (cleanState v).2.isSome) (.goto (fun _ => .inr i)) (.goto (fun _ => .inr (next j))))
  else .push .vars (fun v => (cleanState v).1) (.load (fun _ => .inl Source.initialState) .halt)

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl (.inl .yes) => .load (fun _ => .inr (true,none)) (.goto (fun _ => .inr 0))
  | .inl (.inl .no) => .load (fun _ => .inr (false,none)) (.goto (fun _ => .inr 0))
  | .inl l => lift (Shared.ComplexityBridge.TM2WitnessLookup.program l)
  | .inr i => cleanProgram i

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .vars
  k₁ := .vars
  Γ := fun _ => Bool
  Λ := Label
  main := .inl (.inl .start)
  σ := State
  initialState := .inl Source.initialState
  m := program

def terminal (q : Source.Cfg) : Prop := q.l = some (.inl .yes) ∨ q.l = some (.inl .no)
noncomputable instance : DecidablePred terminal := fun _ => Classical.propDecidable _
theorem stable (q : Source.Cfg) (h : terminal q) : Source.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some (Sum.inl Shared.ComplexityBridge.TM2WitnessLookup.Phase.yes) ∨ l = some (Sum.inl Shared.ComplexityBridge.TM2WitnessLookup.Phase.no) at h
    rcases h with h | h <;> subst l <;> rfl

theorem source_step (q : Source.Cfg) (h : ¬ terminal q) :
    machine.step (embed q) = (Source.step q).map embed := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | inl p => cases p with
        | yes => exact False.elim (h (Or.inl rfl))
        | no => exact False.elim (h (Or.inr rfl))
        | start | copy | restore | clearLeft | clearRight =>
          change some (stepAux (lift (Shared.ComplexityBridge.TM2WitnessLookup.program _)) (.inl v) S) = _
          rw [lift_aux]; rfl
      | inr l =>
        change some (stepAux (lift (Shared.ComplexityBridge.TM2WitnessLookup.program _)) (.inl v) S) = _
        rw [lift_aux]; rfl

def cleanCfg (i : Fin 7) (answer : Bool) (flag : Option Bool) (S : Key → List Bool) : machine.Cfg :=
  ⟨some (.inr i),.inr (answer,flag),S⟩

theorem dispatch (q : Source.Cfg) (answer : Bool)
    (h : q.l = some (.inl (if answer then .yes else .no))) :
    machine.step (embed q) = some (cleanCfg 0 answer none q.stk) := by
  cases q with
  | mk l v S => cases answer <;> simp only [Bool.false_eq_true,if_false,if_true] at h <;> subst l <;> rfl

theorem clean_cons (i : Fin 6) (answer : Bool) (flag : Option Bool) (S : Key → List Bool) (b : Bool) (xs : List Bool) :
    machine.step (cleanCfg (stage i) answer flag (Function.update S (keyOf i) (b::xs))) =
      some (cleanCfg (stage i) answer (some b) (Function.update S (keyOf i) xs)) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cleanCfg,program,cleanProgram,stage,dif_pos i.isLt,
    stepAux,cleanState,Function.update_self,List.head?_cons,Option.isSome_some,List.tail_cons,Bool.cond_true]
  congr 1; congr 1
  exact Function.update_idem _ _ _

theorem clean_nil (i : Fin 6) (answer : Bool) (flag : Option Bool) (S : Key → List Bool) :
    machine.step (cleanCfg (stage i) answer flag (Function.update S (keyOf i) [])) =
      some (cleanCfg (next i) answer none (Function.update S (keyOf i) [])) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cleanCfg,program,cleanProgram,stage,dif_pos i.isLt,
    stepAux,cleanState,Function.update_self,List.head?_nil,Option.isSome_none,List.tail_nil,Bool.cond_false]
  congr 1; congr 1
  exact Function.update_idem _ _ _

theorem sweep_one (i : Fin 6) (answer : Bool) (flag : Option Bool) (S : Key → List Bool) (xs : List Bool) :
    runSteps machine.step (xs.length+1) (cleanCfg (stage i) answer flag (Function.update S (keyOf i) xs)) =
      some (cleanCfg (next i) answer none (Function.update S (keyOf i) [])) := by
  induction xs generalizing flag with
  | nil => exact clean_nil i answer flag S
  | cons b xs ih =>
    rw [List.length_cons,show xs.length+1+1 = (xs.length+1)+1 by omega,runSteps_front,clean_cons]
    exact ih (some b)

theorem sweep_suffix (answer : Bool) (bound n : Nat) :
    ∀ (a : Nat) (ha : a+n = 6) (S : Key → List Bool) (flag : Option Bool),
      (∀ k, (keyIndex k).val < a → S k = []) → (∀ k, (S k).length ≤ bound) →
      ∃ t ≤ n*(bound+1), ∃ f,
        runSteps machine.step t (cleanCfg ⟨a,by omega⟩ answer flag S) =
          some (cleanCfg done answer f (fun _ => [])) := by
  induction n with
  | zero =>
    intro a ha S flag hempty hbound
    have ae : a = 6 := by omega
    have hS : S = fun _ => [] := by
      funext k; apply hempty; have hk := (keyIndex k).isLt; omega
    subst S
    have hl : (⟨a,by omega⟩ : Fin 7) = done := by apply Fin.ext; simp [done,ae]
    refine ⟨0,by simp,flag,?_⟩
    rw [hl]; rfl
  | succ n ih =>
    intro a ha S flag hempty hbound
    have halt : a < 6 := by omega
    let i : Fin 6 := ⟨a,halt⟩
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
    have hstage : stage i = (⟨a,by omega⟩ : Fin 7) := by apply Fin.ext; rfl
    have hnext : next i = (⟨a+1,by omega⟩ : Fin 7) := by apply Fin.ext; rfl
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
  have hn : ¬done.val < 6 := by simp [done]
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cleanCfg,program,cleanProgram,dif_neg hn,stepAux,cleanState]
  congr 1
  change Cfg.mk none (.inl Source.initialState : State) (Function.update (fun _ : Key => ([] : List Bool)) Shared.ComplexityBridge.TM2WitnessLookup.Key.vars [answer]) = _
  congr 1; funext k; cases k <;> simp [Function.update,Turing.haltList,machine] <;> rfl

theorem sweep_all (answer : Bool) (S : Key → List Bool) (bound : Nat)
    (hbound : ∀ k, (S k).length ≤ bound) :
    ∃ t ≤ 6*(bound+1)+1, runSteps machine.step t (cleanCfg 0 answer none S) =
      some (Turing.haltList machine [answer]) := by
  obtain ⟨t,ht,flag,hr⟩ := sweep_suffix answer bound 6 0 (by omega) S none (by intro k hk; omega) hbound
  refine ⟨t+1,by omega,?_⟩
  change runSteps machine.step (t+1) (cleanCfg ⟨0,by omega⟩ answer none S) = _
  rw [runSteps_add,hr]
  exact finish answer flag

noncomputable def loopBound (size : Nat) : Nat :=
  (size+1)*Shared.ComplexityBridge.TM2WitnessLookup.iterationBound size

noncomputable def outputBound (size : Nat) : Nat :=
  loopBound size + 1 + 6*(size + loopBound size*Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source + 1) + 1

/-- The loaded lookup and its six-stack cleanup are one finite machine. Every
residual stack is bounded and charged before the exact halt/output state. -/
theorem loaded_run (vars : List (List Bool)) (witness query : List Bool) :
    let size := (Shared.ComplexityBridge.TM2WitnessLookup.frames vars).length+witness.length+query.length
    let start := Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none
      (Shared.ComplexityBridge.TM2WitnessLookup.frames vars) witness query [] [] []
    ∃ t ≤ outputBound size, runSteps machine.step t (embed start) =
      some (Turing.haltList machine [Shared.ComplexityBridge.RawCNFLookup.lookup vars witness query]) := by
  let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
  let size := frame.length+witness.length+query.length
  let B := frame.length+query.length
  let P := loopBound size
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source
  let start := Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none frame witness query [] [] []
  let answer := Shared.ComplexityBridge.RawCNFLookup.lookup vars witness query
  obtain ⟨n,hn,q,hr,hq⟩ := Shared.ComplexityBridge.TM2WitnessLookup.lookup_progress vars witness query false false none
  change n ≤ (B+1)*Shared.ComplexityBridge.TM2WitnessLookup.iterationBound B at hn
  change runSteps Source.step n start = some q at hr
  change q.l = some (.inl (if answer then .yes else .no)) at hq
  have hB : B ≤ size := by dsimp [B,size]; omega
  have hm := Nat.mul_le_mul (show B+1 ≤ size+1 by omega) (Shared.ComplexityBridge.TM2WitnessLookup.iterationBound_mono hB)
  have hnP : n ≤ P := by dsimp [P,loopBound]; exact le_trans hn hm
  have hterminal : terminal q := by
    unfold terminal
    cases he : answer with
    | false => right; simpa [he] using hq
    | true => left; simpa [he] using hq
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Source.step machine.step embed terminal stable source_step n start q hterminal hr
  have hstart : ∀ k : Key, (start.stk k).length ≤ size := by
    intro k
    cases k <;> simp [start,Shared.ComplexityBridge.TM2WitnessLookup.cfg,
      Shared.ComplexityBridge.TM2WitnessLookup.stackVals,size] <;> omega
  have hstack : ∀ k : Key, (q.stk k).length ≤ size+P*D := by
    intro k
    have hh := Shared.ComplexityBridge.TM2GenericStackBound.run_length Source n start q hr k
    have hm := Nat.mul_le_mul_right D hnP
    have hs := hstart k
    change (q.stk k).length ≤ (start.stk k).length+n*D at hh
    omega
  obtain ⟨c,hc,hcr⟩ := sweep_all answer q.stk (size+P*D) hstack
  refine ⟨a+1+c,?_,?_⟩
  · change a+1+c ≤ outputBound size
    change a+1+c ≤ P+1+6*(size+P*D+1)+1
    omega
  · change runSteps machine.step (a+1+c) (embed start) = _
    rw [show a+1+c = a+(1+c) by omega,runSteps_add,har]
    change runSteps machine.step (1+c) (embed q) = _
    rw [runSteps_add]
    change (machine.step (embed q)).bind (runSteps machine.step c) = _
    rw [dispatch q answer hq]
    exact hcr

/-- The output bit is exactly the verifier's assignment to the decoded query. -/
theorem loaded_run_assignment (vars : List (List Bool)) (witness query : List Bool) :
    let size := (Shared.ComplexityBridge.TM2WitnessLookup.frames vars).length+witness.length+query.length
    let start := Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none
      (Shared.ComplexityBridge.TM2WitnessLookup.frames vars) witness query [] [] []
    ∃ t ≤ outputBound size, runSteps machine.step t (embed start) =
      some (Turing.haltList machine [Shared.ComplexityBridge.CNF.assignment
        (vars.map Computability.decodeNat) witness (Computability.decodeNat query)]) := by
  simpa [Shared.ComplexityBridge.RawCNFLookup.lookup_correct] using loaded_run vars witness query

/-- An explicit polynomial in the total length of the loaded raw stacks. -/
noncomputable def timePolynomial : Polynomial Nat :=
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source
  let E := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Shared.ComplexityBridge.TM2WitnessLookup.Compare
  let I := Polynomial.C 8*(Polynomial.X+Polynomial.C 2) + Polynomial.C 2*((Polynomial.X+Polynomial.C 2)*Polynomial.C E)
  let P := (Polynomial.X+Polynomial.C 1)*I
  P+Polynomial.C 1+Polynomial.C 6*(Polynomial.X+P*Polynomial.C D+Polynomial.C 1)+Polynomial.C 1

theorem timePolynomial_eval (n : Nat) : timePolynomial.eval n = outputBound n := by
  simp [timePolynomial,outputBound,loopBound,Shared.ComplexityBridge.TM2WitnessLookup.iterationBound]

/-- Polynomial form of the bound for the loaded boundary. -/
theorem loaded_run_polynomial (vars : List (List Bool)) (witness query : List Bool) :
    let size := (Shared.ComplexityBridge.TM2WitnessLookup.frames vars).length+witness.length+query.length
    let start := Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none
      (Shared.ComplexityBridge.TM2WitnessLookup.frames vars) witness query [] [] []
    ∃ t ≤ timePolynomial.eval size, runSteps machine.step t (embed start) =
      some (Turing.haltList machine [Shared.ComplexityBridge.RawCNFLookup.lookup vars witness query]) := by
  simpa [timePolynomial_eval] using loaded_run vars witness query

namespace Fixtures
example : (runSteps machine.step 9 (embed (Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none [] [] [] [] [] []))).map
    (fun q => (q.l.isNone,q.stk .vars)) = some (true,[false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .vars)) (runSteps machine.step 9
    (embed (Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none [] [] [] [] [] []))) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 29 (embed (Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none
    (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false]]) [true] [false,true] [] [] []))).map
    (fun q => (q.l.isNone,q.stk .vars,q.stk .query)) = some (true,[true],[]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk .vars,q.stk .query)) (runSteps machine.step 29
    (embed (Shared.ComplexityBridge.TM2WitnessLookup.cfg .start false false none
      (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false]]) [true] [false,true] [] [] []))) : Option (Bool × List Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2WitnessOutput
