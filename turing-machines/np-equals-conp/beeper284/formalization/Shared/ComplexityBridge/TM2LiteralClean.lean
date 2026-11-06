import Shared.ComplexityBridge.TM2LiteralPreserve

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2LiteralClean
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Source := Shared.ComplexityBridge.TM2LiteralPreserve.machine
abbrev Key := Shared.ComplexityBridge.TM2LiteralPreserve.Key
abbrev SKey := Shared.ComplexityBridge.TM2LiteralPreserve.SKey
abbrev Extra := Shared.ComplexityBridge.TM2LiteralPreserve.Extra
abbrev Result := Shared.ComplexityBridge.TM2LiteralEval.Result
abbrev SourceLabel := Shared.ComplexityBridge.TM2LiteralPreserve.Label
abbrev SourceState := Shared.ComplexityBridge.TM2LiteralPreserve.State
abbrev Label := SourceLabel ⊕ (Fin 7 ⊕ Result)
abbrev State := SourceState ⊕ (Result × Option Bool)
def sourceState : State → SourceState | .inl v => v | _ => Source.initialState
def cleanState : State → Result × Option Bool | .inr v => v | _ => (.invalid,none)
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

def keyOf (i : Fin 6) : SKey :=
  match i.val with | 0 => .vars | 1 => .witness | 2 => .query | 3 => .scratch | 4 => .left | _ => .right
def keyIndex : SKey → Fin 6
  | .vars => 0 | .witness => 1 | .query => 2 | .scratch => 3 | .left => 4 | .right => 5
@[simp] theorem keyOf_index (k : SKey) : keyOf (keyIndex k) = k := by cases k <;> rfl
@[simp] theorem index_keyOf (i : Fin 6) : keyIndex (keyOf i) = i := by fin_cases i <;> rfl

def stage (i : Fin 6) : Fin 7 := ⟨i.val,by omega⟩
def next (i : Fin 6) : Fin 7 := ⟨i.val+1,by omega⟩
def done : Fin 7 := ⟨6,by decide⟩

def cleanProgram (i : Fin 7) : Stmt (fun _ : Key => Bool) Label State :=
  if h : i.val < 6 then
    let j : Fin 6 := ⟨i.val,h⟩
    .pop (.inl (keyOf j)) (fun v x => .inr ((cleanState v).1,x))
      (.branch (fun v => (cleanState v).2.isSome) (.goto (fun _ => .inr (.inl i))) (.goto (fun _ => .inr (.inl (next j)))))
  else .load (fun v => .inr ((cleanState v).1,none))
    (.goto (fun v => .inr (.inr (cleanState v).1)))

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl (.inr (.inr (.inr r))) => .load (fun _ => .inr (r,none)) (.goto (fun _ => .inr (.inl 0)))
  | .inl l => lift (Shared.ComplexityBridge.TM2LiteralPreserve.program l)
  | .inr (.inl i) => cleanProgram i
  | .inr (.inr r) => .goto (fun _ => .inr (.inr r))

def machine : Turing.FinTM2 where
  K := Key
  k₀ := Source.k₀
  k₁ := Source.k₁
  Γ := fun _ => Bool
  Λ := Label
  main := .inl Source.main
  σ := State
  initialState := .inl Source.initialState
  m := program

def terminal (q : Source.Cfg) : Prop := ∃ r : Result, q.l = some (.inr (.inr (.inr r)))
noncomputable instance : DecidablePred terminal := fun _ => Classical.propDecidable _
theorem stable (q : Source.Cfg) (h : terminal q) : Source.step q = some q := by
  rcases h with ⟨r,hr⟩
  cases q with
  | mk l v S =>
    change l = some (.inr (.inr (.inr r))) at hr
    subst l
    rfl

theorem source_step (q : Source.Cfg) (h : ¬ terminal q) :
    machine.step (embed q) = (Source.step q).map embed := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | inl p =>
        change some (stepAux (lift (Shared.ComplexityBridge.TM2LiteralPreserve.program (.inl p))) (.inl v) S) = _
        rw [lift_aux]; rfl
      | inr l => cases l with
        | inl p =>
          change some (stepAux (lift (Shared.ComplexityBridge.TM2LiteralPreserve.program (.inr (.inl p)))) (.inl v) S) = _
          rw [lift_aux]; rfl
        | inr l => cases l with
          | inl p =>
            change some (stepAux (lift (Shared.ComplexityBridge.TM2LiteralPreserve.program (.inr (.inr (.inl p))))) (.inl v) S) = _
            rw [lift_aux]; rfl
          | inr r => exact False.elim (h ⟨r,rfl⟩)

def cleanCfg (i : Fin 7) (answer : Result) (flag : Option Bool) (S : Key → List Bool) : machine.Cfg :=
  ⟨some (.inr (.inl i)),.inr (answer,flag),S⟩

def finalCfg (answer : Result) (E : Extra → List Bool) : machine.Cfg :=
  ⟨some (.inr (.inr answer)),.inr (answer,none),
    Shared.ComplexityBridge.TM2LiteralPreserve.combinedStacks (fun _ => []) E⟩

theorem dispatch (q : Source.Cfg) (answer : Result)
    (h : q.l = some (.inr (.inr (.inr answer)))) :
    machine.step (embed q) = some (cleanCfg 0 answer none q.stk) := by
  cases q with
  | mk l v S =>
    change l = some (.inr (.inr (.inr answer))) at h
    subst l
    rfl

theorem clean_cons (i : Fin 6) (answer : Result) (flag : Option Bool) (S : Key → List Bool) (b : Bool) (xs : List Bool) :
    machine.step (cleanCfg (stage i) answer flag (Function.update S (.inl (keyOf i)) (b::xs))) =
      some (cleanCfg (stage i) answer (some b) (Function.update S (.inl (keyOf i)) xs)) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cleanCfg,program,cleanProgram,stage,dif_pos i.isLt,
    stepAux,cleanState,Function.update_self,List.head?_cons,Option.isSome_some,List.tail_cons,Bool.cond_true]
  congr 1; congr 1
  exact Function.update_idem _ _ _

theorem clean_nil (i : Fin 6) (answer : Result) (flag : Option Bool) (S : Key → List Bool) :
    machine.step (cleanCfg (stage i) answer flag (Function.update S (.inl (keyOf i)) [])) =
      some (cleanCfg (next i) answer none (Function.update S (.inl (keyOf i)) [])) := by
  simp only [Turing.FinTM2.step,Turing.TM2.step,machine,cleanCfg,program,cleanProgram,stage,dif_pos i.isLt,
    stepAux,cleanState,Function.update_self,List.head?_nil,Option.isSome_none,List.tail_nil,Bool.cond_false]
  congr 1; congr 1
  exact Function.update_idem _ _ _

theorem sweep_one (i : Fin 6) (answer : Result) (flag : Option Bool) (S : Key → List Bool) (xs : List Bool) :
    runSteps machine.step (xs.length+1) (cleanCfg (stage i) answer flag (Function.update S (.inl (keyOf i)) xs)) =
      some (cleanCfg (next i) answer none (Function.update S (.inl (keyOf i)) [])) := by
  induction xs generalizing flag with
  | nil => exact clean_nil i answer flag S
  | cons b xs ih =>
    rw [List.length_cons,show xs.length+1+1 = (xs.length+1)+1 by omega,runSteps_front,clean_cons]
    exact ih (some b)

def emptied (S : Key → List Bool) : Key → List Bool :=
  Shared.ComplexityBridge.TM2LiteralPreserve.combinedStacks (fun _ => []) (fun e => S (.inr e))

theorem emptied_update (S : Key → List Bool) (k : SKey) (xs : List Bool) :
    emptied (Function.update S (.inl k) xs) = emptied S := by
  funext key
  cases key with
  | inl k => rfl
  | inr e => simp [emptied,Shared.ComplexityBridge.TM2LiteralPreserve.combinedStacks,Function.update]

theorem sweep_suffix (answer : Result) (bound n : Nat) :
    ∀ (a : Nat) (ha : a+n = 6) (S : Key → List Bool) (flag : Option Bool),
      (∀ k : SKey, (keyIndex k).val < a → S (.inl k) = []) → (∀ k : SKey, (S (.inl k)).length ≤ bound) →
      ∃ t ≤ n*(bound+1), ∃ f,
        runSteps machine.step t (cleanCfg ⟨a,by omega⟩ answer flag S) =
          some (cleanCfg done answer f (emptied S)) := by
  induction n with
  | zero =>
    intro a ha S flag hempty hbound
    have ae : a = 6 := by omega
    have hS : S = emptied S := by
      funext k
      cases k with
      | inl k =>
        have hk := (keyIndex k).isLt
        exact hempty k (by omega)
      | inr k => rfl
    have hl : (⟨a,by omega⟩ : Fin 7) = done := by apply Fin.ext; simp [done,ae]
    refine ⟨0,by simp,flag,?_⟩
    rw [hl,← hS]; rfl
  | succ n ih =>
    intro a ha S flag hempty hbound
    have halt : a < 6 := by omega
    let i : Fin 6 := ⟨a,halt⟩
    let S' := Function.update S (.inl (keyOf i)) []
    have hempty' : ∀ k : SKey, (keyIndex k).val < a+1 → S' (.inl k) = [] := by
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
        have hne : (Sum.inl k : Key) ≠ .inl (keyOf i) := by intro h; exact heq (Sum.inl.inj h)
        simpa [S',Function.update_of_ne hne] using hempty k hlt
    have hbound' : ∀ k : SKey, (S' (.inl k)).length ≤ bound := by
      intro k
      by_cases heq : k = keyOf i
      · subst k; simp [S']
      · have hne : (Sum.inl k : Key) ≠ .inl (keyOf i) := by intro h; exact heq (Sum.inl.inj h)
        simpa [S',Function.update_of_ne hne] using hbound k
    obtain ⟨t,ht,f,hrun⟩ := ih (a+1) (by omega) S' none hempty' hbound'
    have hstage : stage i = (⟨a,by omega⟩ : Fin 7) := by apply Fin.ext; rfl
    have hnext : next i = (⟨a+1,by omega⟩ : Fin 7) := by apply Fin.ext; rfl
    have hone := sweep_one i answer flag S (S (.inl (keyOf i)))
    rw [Function.update_eq_self,hstage,hnext] at hone
    have htbound : (S (.inl (keyOf i))).length+1+t ≤ (n+1)*(bound+1) := by
      have hi := hbound (keyOf i)
      rw [Nat.add_mul,Nat.one_mul]
      omega
    refine ⟨(S (.inl (keyOf i))).length+1+t,by simpa using htbound,f,?_⟩
    rw [runSteps_add,hone]
    simpa [S',emptied_update] using hrun

theorem finish (answer : Result) (flag : Option Bool) (E : Extra → List Bool) :
    machine.step (cleanCfg done answer flag (Shared.ComplexityBridge.TM2LiteralPreserve.combinedStacks (fun _ => []) E)) =
      some (finalCfg answer E) := by
  have hn : ¬done.val < 6 := by simp [done]
  simp [Turing.FinTM2.step,Turing.TM2.step,machine,cleanCfg,program,cleanProgram,dif_neg hn,stepAux,cleanState,finalCfg,done]

theorem sweep_all (answer : Result) (S : Key → List Bool) (bound : Nat)
    (hbound : ∀ k : SKey, (S (.inl k)).length ≤ bound) :
    ∃ t ≤ 6*(bound+1)+1,
      runSteps machine.step t (cleanCfg 0 answer none S) =
        some (finalCfg answer (fun e => S (.inr e))) := by
  obtain ⟨t,ht,flag,hr⟩ := sweep_suffix answer bound 6 0 (by omega) S none (by intro k hk; omega) hbound
  refine ⟨t+1,by omega,?_⟩
  change runSteps machine.step (t+1) (cleanCfg ⟨0,by omega⟩ answer none S) = _
  rw [runSteps_add,hr]
  exact finish answer flag (fun e => S (.inr e))

noncomputable def timePolynomial : Polynomial Nat :=
  let P := Shared.ComplexityBridge.TM2LiteralPreserve.timePolynomial
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source
  P+Polynomial.C 1+Polynomial.C 6*(Polynomial.X+P*Polynomial.C D+Polynomial.C 1)+Polynomial.C 1

theorem timePolynomial_eval (n : Nat) :
    timePolynomial.eval n = Shared.ComplexityBridge.TM2LiteralPreserve.timePolynomial.eval n+1+
      6*(n+Shared.ComplexityBridge.TM2LiteralPreserve.timePolynomial.eval n*
        Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source+1)+1 := by
  simp [timePolynomial]

/-- A finite loaded literal call including copies, evaluation and cleanup.
Every source work stack is empty on return; the occurrence and witness
stacks are intact and the result is encoded in a distinct continuation label. -/
theorem loaded_progress (vars : List (List Bool)) (witness literal : List Bool) :
    let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
    let size := frame.length+witness.length+literal.length
    let answer := match Shared.ComplexityBridge.TM2LiteralEval.evaluate vars witness literal with
      | none => Shared.ComplexityBridge.TM2LiteralEval.Result.invalid | some true => Shared.ComplexityBridge.TM2LiteralEval.Result.yes | some false => Shared.ComplexityBridge.TM2LiteralEval.Result.no
    ∃ t ≤ timePolynomial.eval size,
      runSteps machine.step t (embed (Shared.ComplexityBridge.TM2LiteralPreserve.cfg .scanVars none frame witness [] [] [] literal)) =
        some (finalCfg answer (Shared.ComplexityBridge.TM2LiteralPreserve.extras frame witness [])) := by
  let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
  let size := frame.length+witness.length+literal.length
  let P := Shared.ComplexityBridge.TM2LiteralPreserve.timePolynomial.eval size
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound Source
  let start := Shared.ComplexityBridge.TM2LiteralPreserve.cfg .scanVars none frame witness [] [] [] literal
  let E := Shared.ComplexityBridge.TM2LiteralPreserve.extras frame witness []
  let answer := match Shared.ComplexityBridge.TM2LiteralEval.evaluate vars witness literal with
    | none => Shared.ComplexityBridge.TM2LiteralEval.Result.invalid | some true => Shared.ComplexityBridge.TM2LiteralEval.Result.yes | some false => Shared.ComplexityBridge.TM2LiteralEval.Result.no
  obtain ⟨n,hn,q,hr,hq,hvars,hw,hs,hstack⟩ := Shared.ComplexityBridge.TM2LiteralPreserve.loaded_progress_with_work_bound vars witness literal
  change n ≤ P at hn
  change runSteps Source.step n start = some q at hr
  change q.l = some (.inr (.inr (.inr answer))) at hq
  have hterminal : terminal q := ⟨answer,hq⟩
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Source.step machine.step embed terminal stable source_step n start q hterminal hr
  have hstack' : ∀ k : SKey, (q.stk (.inl k)).length ≤ size+P*D := by
    intro k
    exact hstack k
  obtain ⟨c,hc,hcr⟩ := sweep_all answer q.stk (size+P*D) hstack'
  have hextras : (fun e : Extra => q.stk (.inr e)) = E := by
    funext e
    cases e with
    | vars => exact hvars
    | witness => exact hw
    | scratch => exact hs
  rw [hextras] at hcr
  refine ⟨a+1+c,?_,?_⟩
  · rw [timePolynomial_eval]
    change a+1+c ≤ P+1+6*(size+P*D+1)+1
    omega
  · change runSteps machine.step (a+1+c) (embed start) = some (finalCfg answer E)
    rw [show a+1+c = a+(1+c) by omega,runSteps_add,har]
    change runSteps machine.step (1+c) (embed q) = _
    rw [runSteps_add]
    change (machine.step (embed q)).bind _ = _
    rw [dispatch q answer hq]
    exact hcr


/-- On valid input the continuation is the canonical literal value. -/
theorem loaded_progress_correct (vars : List (List Bool)) (witness literal : List Bool)
    (lit : Shared.ComplexityBridge.CNF.Literal)
    (h : (BitstringEncoding.bitDecode literal : Option Shared.ComplexityBridge.CNF.Literal) = some lit) :
    let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
    let size := frame.length+witness.length+literal.length
    let value := Shared.ComplexityBridge.CNF.evalLiteral
      (Shared.ComplexityBridge.CNF.assignment (vars.map Computability.decodeNat) witness) lit
    ∃ t ≤ timePolynomial.eval size,
      runSteps machine.step t (embed (Shared.ComplexityBridge.TM2LiteralPreserve.cfg .scanVars none frame witness [] [] [] literal)) =
        some (finalCfg (if value then .yes else .no) (Shared.ComplexityBridge.TM2LiteralPreserve.extras frame witness [])) := by
  have he := Shared.ComplexityBridge.TM2LiteralEval.evaluate_correct vars witness literal lit h
  have hr := loaded_progress vars witness literal
  rw [he] at hr
  cases hv : Shared.ComplexityBridge.CNF.evalLiteral
      (Shared.ComplexityBridge.CNF.assignment (vars.map Computability.decodeNat) witness) lit <;> simpa [hv] using hr

/-- Malformed literals reach a separate invalid continuation after cleanup. -/
theorem loaded_progress_invalid (vars : List (List Bool)) (witness literal : List Bool)
    (h : (BitstringEncoding.bitDecode literal : Option Shared.ComplexityBridge.CNF.Literal) = none) :
    let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
    let size := frame.length+witness.length+literal.length
    ∃ t ≤ timePolynomial.eval size,
      runSteps machine.step t (embed (Shared.ComplexityBridge.TM2LiteralPreserve.cfg .scanVars none frame witness [] [] [] literal)) =
        some (finalCfg .invalid (Shared.ComplexityBridge.TM2LiteralPreserve.extras frame witness [])) := by
  have he := (Shared.ComplexityBridge.TM2LiteralEval.evaluate_none_iff vars witness literal).2 h
  simpa [he] using loaded_progress vars witness literal

namespace Fixtures
set_option maxRecDepth 4096 in
example : (runSteps machine.step 48 (embed (Shared.ComplexityBridge.TM2LiteralPreserve.cfg .scanVars none
    (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false]]) [true] [] [] [] [true,false,false,true]))).map
    (fun q => (match q.l with | some (.inr (.inr .yes)) => true | _ => false,
      q.stk (.inr .vars),q.stk (.inr .witness),
      [q.stk (.inl .vars),q.stk (.inl .witness),q.stk (.inl .query),q.stk (.inl .scratch),q.stk (.inl .left),q.stk (.inl .right)])) =
    some (true,Shared.ComplexityBridge.TM2WitnessLookup.frames [[false]],[true],[[],[],[],[],[],[]]) := by
  change (Option.map (fun q => (match q.l with | some (.inr (.inr .yes)) => true | _ => false,
      q.stk (.inr .vars),q.stk (.inr .witness),
      [q.stk (.inl .vars),q.stk (.inl .witness),q.stk (.inl .query),q.stk (.inl .scratch),q.stk (.inl .left),q.stk (.inl .right)]))
    (runSteps machine.step 48 (embed (Shared.ComplexityBridge.TM2LiteralPreserve.cfg .scanVars none
      (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false]]) [true] [] [] [] [true,false,false,true]))) :
      Option (Bool × List Bool × List Bool × List (List Bool))) = _
  decide

example : (runSteps machine.step 18 (embed (Shared.ComplexityBridge.TM2LiteralPreserve.cfg .scanVars none [] [] [] [] [] [false]))).map
    (fun q => match q.l with | some (.inr (.inr .invalid)) => true | _ => false) = some true := by
  change (Option.map (fun q => match q.l with | some (.inr (.inr .invalid)) => true | _ => false)
    (runSteps machine.step 18 (embed (Shared.ComplexityBridge.TM2LiteralPreserve.cfg .scanVars none [] [] [] [] [] [false]))) : Option Bool) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2LiteralClean
