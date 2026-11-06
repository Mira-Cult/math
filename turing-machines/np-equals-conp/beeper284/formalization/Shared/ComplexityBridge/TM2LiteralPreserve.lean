import Shared.ComplexityBridge.TM2LiteralEval

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2LiteralPreserve
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Source := Shared.ComplexityBridge.TM2LiteralEval.machine
abbrev SKey := Shared.ComplexityBridge.TM2LiteralEval.Key
abbrev SLabel := Shared.ComplexityBridge.TM2LiteralEval.Label
abbrev SState := Shared.ComplexityBridge.TM2LiteralEval.State
inductive Extra where | vars | witness | scratch deriving DecidableEq
inductive Phase where | scanVars | restoreVars | scanWitness | restoreWitness | start deriving DecidableEq
instance : Fintype Extra := Fintype.ofList [.vars,.witness,.scratch] (by intro k; cases k <;> simp)
instance : Fintype Phase := Fintype.ofList [.scanVars,.restoreVars,.scanWitness,.restoreWitness,.start] (by intro k; cases k <;> simp)
abbrev Key := SKey ⊕ Extra
abbrev Label := Phase ⊕ SLabel
abbrev State := Option Bool ⊕ SState

def copyState : State → Option Bool | .inl v => v | _ => none
def sourceState : State → SState | .inr v => v | _ => Source.initialState

def combinedStacks (S : SKey → List Bool) (E : Extra → List Bool) : Key → List Bool
  | .inl k => S k | .inr k => E k

def embed (E : Extra → List Bool) (q : Source.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map Sum.inr,.inr q.var,combinedStacks q.stk E⟩

theorem stacks_update (S : SKey → List Bool) (E : Extra → List Bool) (k : SKey) (v : List Bool) :
    combinedStacks (Function.update S k v) E = Function.update (combinedStacks S E) (.inl k) v := by
  funext i; cases i with
  | inl i => by_cases h : i = k <;> simp [combinedStacks,Function.update,h]
  | inr i => simp [combinedStacks,Function.update]

def lift : Stmt (fun _ : SKey => Bool) SLabel SState → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push (.inl j) (fun v => f (sourceState v)) (lift q)
  | .peek j f q => .peek (.inl j) (fun v h => .inr (f (sourceState v) h)) (lift q)
  | .pop j f q => .pop (.inl j) (fun v h => .inr (f (sourceState v) h)) (lift q)
  | .load f q => .load (fun v => .inr (f (sourceState v))) (lift q)
  | .branch f q r => .branch (fun v => f (sourceState v)) (lift q) (lift r)
  | .goto f => .goto (fun v => .inr (f (sourceState v)))
  | .halt => .halt

theorem lift_aux (q : Source.Stmt) (v : SState) (S : SKey → List Bool) (E : Extra → List Bool) :
    stepAux (lift q) (.inr v) (combinedStacks S E) = embed E (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih => simp only [lift,stepAux,sourceState,combinedStacks]; rw [← stacks_update S E j (f v::S j)]; exact ih _ _
  | peek j f q ih => simp only [lift,stepAux,sourceState,combinedStacks]; exact ih _ _
  | pop j f q ih => simp only [lift,stepAux,sourceState,combinedStacks]; rw [← stacks_update S E j (S j).tail]; exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [lift,stepAux,sourceState,h,ihq,ihr]

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl .scanVars => .pop (.inr .vars) (fun _ h => .inl h)
      (.branch (fun v => (copyState v).isSome)
        (.push (.inr .scratch) (fun v => (copyState v).getD false) (.goto (fun _ => .inl .scanVars)))
        (.goto (fun _ => .inl .restoreVars)))
  | .inl .restoreVars => .pop (.inr .scratch) (fun _ h => .inl h)
      (.branch (fun v => (copyState v).isSome)
        (.push (.inr .vars) (fun v => (copyState v).getD false)
          (.push (.inl .vars) (fun v => (copyState v).getD false) (.goto (fun _ => .inl .restoreVars))))
        (.goto (fun _ => .inl .scanWitness)))
  | .inl .scanWitness => .pop (.inr .witness) (fun _ h => .inl h)
      (.branch (fun v => (copyState v).isSome)
        (.push (.inr .scratch) (fun v => (copyState v).getD false) (.goto (fun _ => .inl .scanWitness)))
        (.goto (fun _ => .inl .restoreWitness)))
  | .inl .restoreWitness => .pop (.inr .scratch) (fun _ h => .inl h)
      (.branch (fun v => (copyState v).isSome)
        (.push (.inr .witness) (fun v => (copyState v).getD false)
          (.push (.inl .witness) (fun v => (copyState v).getD false) (.goto (fun _ => .inl .restoreWitness))))
        (.goto (fun _ => .inl .start)))
  | .inl .start => .load (fun _ => .inr Source.initialState) (.goto (fun _ => .inr Source.main))
  | .inr l => lift (Shared.ComplexityBridge.TM2LiteralEval.program l)

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .inr .vars
  k₁ := .inl .left
  Γ := fun _ => Bool
  Λ := Label
  main := .inl .scanVars
  σ := State
  initialState := .inl none
  m := program

theorem source_step (E : Extra → List Bool) (q : Source.Cfg) :
    machine.step (embed E q) = (Source.step q).map (embed E) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l =>
      change some (stepAux (lift (Shared.ComplexityBridge.TM2LiteralEval.program l)) (.inr v) (combinedStacks S E)) = _
      rw [lift_aux]; rfl

theorem source_run (E : Extra → List Bool) (n : Nat) (q : Source.Cfg) :
    runSteps machine.step n (embed E q) = (runSteps Source.step n q).map (embed E) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front,source_step,runSteps_front]
    cases hs : Source.step q with
    | none => rfl
    | some next => exact ih next

def extras (vars witness scratch : List Bool) : Extra → List Bool
  | .vars => vars | .witness => witness | .scratch => scratch

def sourceStacks (vars witness literal : List Bool) : SKey → List Bool :=
  Shared.ComplexityBridge.TM2WitnessLookup.stackVals vars witness [] [] literal []

def cfg (l : Phase) (flag : Option Bool) (vars witness tmp copiesVar copiesWitness literal : List Bool) : machine.Cfg :=
  ⟨some (.inl l),.inl flag,combinedStacks (sourceStacks copiesVar copiesWitness literal) (extras vars witness tmp)⟩

theorem scanVars_cons (v : Option Bool) (b : Bool) (vs w tmp cv cw lit : List Bool) :
    machine.step (cfg .scanVars v (b::vs) w tmp cv cw lit) = some (cfg .scanVars (some b) vs w (b::tmp) cv cw lit) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2
  funext k
  cases k with
  | inl k =>
    cases k <;> simp [combinedStacks,sourceStacks,extras,Shared.ComplexityBridge.TM2WitnessLookup.stackVals,Function.update,copyState]
    all_goals try rfl
    all_goals intro h; cases h
  | inr k =>
    cases k <;> simp [combinedStacks,sourceStacks,extras,Function.update,copyState]
    all_goals try rfl
    all_goals intro h; cases h

theorem scanVars_nil (v : Option Bool) (w tmp cv cw lit : List Bool) :
    machine.step (cfg .scanVars v [] w tmp cv cw lit) = some (cfg .restoreVars none [] w tmp cv cw lit) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2
  funext k
  cases k with
  | inl k =>
    cases k <;> simp [combinedStacks,sourceStacks,extras,Shared.ComplexityBridge.TM2WitnessLookup.stackVals,Function.update,copyState]
    all_goals try rfl
    all_goals intro h; cases h
  | inr k =>
    cases k <;> simp [combinedStacks,sourceStacks,extras,Function.update,copyState]
    all_goals try rfl
    all_goals intro h; cases h

theorem restoreVars_cons (v : Option Bool) (b : Bool) (vs w tmp cv cw lit : List Bool) :
    machine.step (cfg .restoreVars v vs w (b::tmp) cv cw lit) = some (cfg .restoreVars (some b) (b::vs) w tmp (b::cv) cw lit) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2
  funext k
  cases k with
  | inl k =>
    cases k <;> simp [combinedStacks,sourceStacks,extras,Shared.ComplexityBridge.TM2WitnessLookup.stackVals,Function.update,copyState]
    all_goals try rfl
    all_goals intro h; cases h
  | inr k =>
    cases k <;> simp [combinedStacks,sourceStacks,extras,Function.update,copyState]
    all_goals try rfl
    all_goals intro h; cases h

theorem restoreVars_nil (v : Option Bool) (vs w cv cw lit : List Bool) :
    machine.step (cfg .restoreVars v vs w [] cv cw lit) = some (cfg .scanWitness none vs w [] cv cw lit) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2
  funext k
  cases k with
  | inl k =>
    cases k <;> simp [combinedStacks,sourceStacks,extras,Shared.ComplexityBridge.TM2WitnessLookup.stackVals,Function.update,copyState]
    all_goals try rfl
    all_goals intro h; cases h
  | inr k =>
    cases k <;> simp [combinedStacks,sourceStacks,extras,Function.update,copyState]
    all_goals try rfl
    all_goals intro h; cases h

theorem scanWitness_cons (v : Option Bool) (b : Bool) (vs w tmp cv cw lit : List Bool) :
    machine.step (cfg .scanWitness v vs (b::w) tmp cv cw lit) = some (cfg .scanWitness (some b) vs w (b::tmp) cv cw lit) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2
  funext k
  cases k with
  | inl k =>
    cases k <;> simp [combinedStacks,sourceStacks,extras,Shared.ComplexityBridge.TM2WitnessLookup.stackVals,Function.update,copyState]
    all_goals try rfl
    all_goals intro h; cases h
  | inr k =>
    cases k <;> simp [combinedStacks,sourceStacks,extras,Function.update,copyState]
    all_goals try rfl
    all_goals intro h; cases h

theorem scanWitness_nil (v : Option Bool) (vs tmp cv cw lit : List Bool) :
    machine.step (cfg .scanWitness v vs [] tmp cv cw lit) = some (cfg .restoreWitness none vs [] tmp cv cw lit) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2
  funext k
  cases k with
  | inl k =>
    cases k <;> simp [combinedStacks,sourceStacks,extras,Shared.ComplexityBridge.TM2WitnessLookup.stackVals,Function.update,copyState]
    all_goals try rfl
    all_goals intro h; cases h
  | inr k =>
    cases k <;> simp [combinedStacks,sourceStacks,extras,Function.update,copyState]
    all_goals try rfl
    all_goals intro h; cases h

theorem restoreWitness_cons (v : Option Bool) (b : Bool) (vs w tmp cv cw lit : List Bool) :
    machine.step (cfg .restoreWitness v vs w (b::tmp) cv cw lit) = some (cfg .restoreWitness (some b) vs (b::w) tmp cv (b::cw) lit) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2
  funext k
  cases k with
  | inl k =>
    cases k <;> simp [combinedStacks,sourceStacks,extras,Shared.ComplexityBridge.TM2WitnessLookup.stackVals,Function.update,copyState]
    all_goals try rfl
    all_goals intro h; cases h
  | inr k =>
    cases k <;> simp [combinedStacks,sourceStacks,extras,Function.update,copyState]
    all_goals try rfl
    all_goals intro h; cases h

theorem restoreWitness_nil (v : Option Bool) (vs w cv cw lit : List Bool) :
    machine.step (cfg .restoreWitness v vs w [] cv cw lit) = some (cfg .start none vs w [] cv cw lit) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2
  funext k
  cases k with
  | inl k =>
    cases k <;> simp [combinedStacks,sourceStacks,extras,Shared.ComplexityBridge.TM2WitnessLookup.stackVals,Function.update,copyState]
    all_goals try rfl
    all_goals intro h; cases h
  | inr k =>
    cases k <;> simp [combinedStacks,sourceStacks,extras,Function.update,copyState]
    all_goals try rfl
    all_goals intro h; cases h

theorem scanVars_loop (vs w tmp cv cw lit : List Bool) (v : Option Bool) :
    ∃ z, runSteps machine.step vs.length (cfg .scanVars v vs w tmp cv cw lit) =
      some (cfg .scanVars z [] w (vs.reverse ++ tmp) cv cw lit) := by
  induction vs generalizing v tmp with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons b vs ih =>
    obtain ⟨z,h⟩ := ih (b::tmp) (some b)
    refine ⟨z,?_⟩
    rw [List.length_cons,runSteps_front,scanVars_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem restoreVars_loop (tmp vs w cv cw lit : List Bool) (v : Option Bool) :
    ∃ z, runSteps machine.step tmp.length (cfg .restoreVars v vs w tmp cv cw lit) =
      some (cfg .restoreVars z (tmp.reverse ++ vs) w [] (tmp.reverse ++ cv) cw lit) := by
  induction tmp generalizing v vs cv with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons b tmp ih =>
    obtain ⟨z,h⟩ := ih (b::vs) (b::cv) (some b)
    refine ⟨z,?_⟩
    rw [List.length_cons,runSteps_front,restoreVars_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem scanWitness_loop (w vs tmp cv cw lit : List Bool) (v : Option Bool) :
    ∃ z, runSteps machine.step w.length (cfg .scanWitness v vs w tmp cv cw lit) =
      some (cfg .scanWitness z vs [] (w.reverse ++ tmp) cv cw lit) := by
  induction w generalizing v tmp with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons b w ih =>
    obtain ⟨z,h⟩ := ih (b::tmp) (some b)
    refine ⟨z,?_⟩
    rw [List.length_cons,runSteps_front,scanWitness_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem restoreWitness_loop (tmp vs w cv cw lit : List Bool) (v : Option Bool) :
    ∃ z, runSteps machine.step tmp.length (cfg .restoreWitness v vs w tmp cv cw lit) =
      some (cfg .restoreWitness z vs (tmp.reverse ++ w) [] cv (tmp.reverse ++ cw) lit) := by
  induction tmp generalizing v w cw with
  | nil => exact ⟨v,by simp [runSteps]⟩
  | cons b tmp ih =>
    obtain ⟨z,h⟩ := ih (b::w) (b::cw) (some b)
    refine ⟨z,?_⟩
    rw [List.length_cons,runSteps_front,restoreWitness_cons]
    simpa [List.reverse_cons,List.append_assoc] using h

theorem dispatch_start (vars witness literal : List Bool) :
    machine.step (cfg .start none vars witness [] vars witness literal) =
      some (embed (extras vars witness []) (Shared.ComplexityBridge.TM2LiteralEval.loaded vars witness literal)) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2
  funext k
  cases k with
  | inl k => cases k <;> simp [combinedStacks,sourceStacks,extras,Shared.ComplexityBridge.TM2WitnessLookup.stackVals,
      Shared.ComplexityBridge.TM2LiteralEval.loaded,Shared.ComplexityBridge.TM2LiteralEval.pemb,
      Shared.ComplexityBridge.TM2LiteralEval.pstacks,Turing.initList,Shared.ComplexityBridge.TM2LiteralEval.Parse,
      Shared.ComplexityBridge.TM2LiteralParse.machine,Shared.ComplexityBridge.TM2Undelimit.machine] <;> rfl
  | inr k => cases k <;> rfl

/-- Copy both inputs, restore the originals and enter the finite literal
machine. Each pop and both terminal empty-stack checks are counted. -/
theorem copy_and_start (vars witness literal : List Bool) :
    runSteps machine.step (2*vars.length+2*witness.length+5)
      (cfg .scanVars none vars witness [] [] [] literal) =
    some (embed (extras vars witness []) (Shared.ComplexityBridge.TM2LiteralEval.loaded vars witness literal)) := by
  obtain ⟨a,ha⟩ := scanVars_loop vars witness [] [] [] literal none
  simp only [List.append_nil] at ha
  obtain ⟨b,hb⟩ := restoreVars_loop vars.reverse [] witness [] [] literal none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hb
  obtain ⟨c,hc⟩ := scanWitness_loop witness vars [] vars [] literal none
  simp only [List.append_nil] at hc
  obtain ⟨d,hd⟩ := restoreWitness_loop witness.reverse vars [] vars [] literal none
  simp only [List.reverse_reverse,List.length_reverse,List.append_nil] at hd
  have hcost : 2*vars.length+2*witness.length+5 = vars.length+(1+(vars.length+(1+(witness.length+(1+(witness.length+(1+1))))))) := by omega
  rw [hcost,runSteps_add,ha]
  change runSteps machine.step (1+(vars.length+(1+(witness.length+(1+(witness.length+(1+1))))))) _ = _
  rw [runSteps_add]
  change (machine.step (cfg .scanVars a [] witness vars.reverse [] [] literal)).bind _ = _
  rw [scanVars_nil]
  change runSteps machine.step (vars.length+(1+(witness.length+(1+(witness.length+(1+1)))))) _ = _
  rw [runSteps_add,hb]
  change runSteps machine.step (1+(witness.length+(1+(witness.length+(1+1))))) _ = _
  rw [runSteps_add]
  change (machine.step (cfg .restoreVars b vars witness [] vars [] literal)).bind _ = _
  rw [restoreVars_nil]
  change runSteps machine.step (witness.length+(1+(witness.length+(1+1)))) _ = _
  rw [runSteps_add,hc]
  change runSteps machine.step (1+(witness.length+(1+1))) _ = _
  rw [runSteps_add]
  change (machine.step (cfg .scanWitness c vars [] witness.reverse vars [] literal)).bind _ = _
  rw [scanWitness_nil]
  change runSteps machine.step (witness.length+(1+1)) _ = _
  rw [runSteps_add,hd]
  simp only [Option.bind_some]
  change runSteps machine.step (1+1) _ = _
  rw [runSteps_add]
  change (machine.step (cfg .restoreWitness d vars witness [] vars witness literal)).bind _ = _
  rw [restoreWitness_nil]
  exact dispatch_start vars witness literal

/-- The complete loaded call, including both copies, returns the literal
result while retaining the exact original occurrence and witness bits. -/
theorem loaded_progress (vars : List (List Bool)) (witness literal : List Bool) :
    let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
    let size := frame.length+witness.length+literal.length
    ∃ t ≤ 2*frame.length+2*witness.length+5+Shared.ComplexityBridge.TM2LiteralEval.timePolynomial.eval size,
      ∃ q : machine.Cfg,
        runSteps machine.step t (cfg .scanVars none frame witness [] [] [] literal) = some q ∧
        q.l = some (.inr (.inr (.inr (match Shared.ComplexityBridge.TM2LiteralEval.evaluate vars witness literal with
          | none => .invalid | some true => .yes | some false => .no)))) ∧
        q.stk (.inr .vars) = frame ∧ q.stk (.inr .witness) = witness ∧ q.stk (.inr .scratch) = [] := by
  let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
  let E := extras frame witness []
  obtain ⟨t,ht,q,hr,hlabel⟩ := Shared.ComplexityBridge.TM2LiteralEval.loaded_progress_polynomial vars witness literal
  have hrun := source_run E t (Shared.ComplexityBridge.TM2LiteralEval.loaded frame witness literal)
  rw [hr] at hrun
  refine ⟨2*frame.length+2*witness.length+5+t,by dsimp [frame] at *; omega,embed E q,?_,?_,?_,?_,?_⟩
  · change runSteps machine.step ((2*frame.length+2*witness.length+5)+t) _ = _
    rw [runSteps_add,copy_and_start]
    exact hrun
  · change (embed E q).l = _
    simp [embed,hlabel]
    rfl
  · rfl
  · rfl
  · rfl

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 2*Polynomial.X+Polynomial.C 5+Shared.ComplexityBridge.TM2LiteralEval.timePolynomial

theorem timePolynomial_eval (n : Nat) :
    timePolynomial.eval n = 2*n+5+Shared.ComplexityBridge.TM2LiteralEval.timePolynomial.eval n := by
  simp [timePolynomial]

/-- A single explicit polynomial includes copying, restoration, literal
parsing, witness lookup and the final result transition. -/
theorem loaded_progress_polynomial (vars : List (List Bool)) (witness literal : List Bool) :
    let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
    let size := frame.length+witness.length+literal.length
    ∃ t ≤ timePolynomial.eval size, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .scanVars none frame witness [] [] [] literal) = some q ∧
      q.l = some (.inr (.inr (.inr (match Shared.ComplexityBridge.TM2LiteralEval.evaluate vars witness literal with
        | none => .invalid | some true => .yes | some false => .no)))) ∧
      q.stk (.inr .vars) = frame ∧ q.stk (.inr .witness) = witness ∧ q.stk (.inr .scratch) = [] := by
  obtain ⟨t,ht,q,hr,hlabel,hvars,hw,hs⟩ := loaded_progress vars witness literal
  refine ⟨t,?_,q,hr,hlabel,hvars,hw,hs⟩
  rw [timePolynomial_eval]
  omega


/-- The remaining working stacks have an explicit polynomial size bound,
which a later cleanup loop can charge before reusing this call boundary. -/
theorem loaded_progress_with_work_bound (vars : List (List Bool)) (witness literal : List Bool) :
    let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
    let size := frame.length+witness.length+literal.length
    let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound machine
    ∃ t ≤ timePolynomial.eval size, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .scanVars none frame witness [] [] [] literal) = some q ∧
      q.l = some (.inr (.inr (.inr (match Shared.ComplexityBridge.TM2LiteralEval.evaluate vars witness literal with
        | none => .invalid | some true => .yes | some false => .no)))) ∧
      q.stk (.inr .vars) = frame ∧ q.stk (.inr .witness) = witness ∧ q.stk (.inr .scratch) = [] ∧
      ∀ k : SKey, (q.stk (.inl k)).length ≤ size+timePolynomial.eval size*D := by
  let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
  let size := frame.length+witness.length+literal.length
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound machine
  let start := cfg .scanVars none frame witness [] [] [] literal
  obtain ⟨t,ht,q,hr,hlabel,hvars,hw,hs⟩ := loaded_progress_polynomial vars witness literal
  change t ≤ timePolynomial.eval size at ht
  change runSteps machine.step t start = some q at hr
  refine ⟨t,ht,q,hr,hlabel,hvars,hw,hs,?_⟩
  intro k
  have hh := Shared.ComplexityBridge.TM2GenericStackBound.run_length machine t start q hr (.inl k)
  have hm := Nat.mul_le_mul_right D ht
  have hstart : (start.stk (.inl k)).length ≤ size := by
    cases k <;> simp [start,cfg,combinedStacks,sourceStacks,
      Shared.ComplexityBridge.TM2WitnessLookup.stackVals,size] <;> omega
  change (q.stk (.inl k)).length ≤ (start.stk (.inl k)).length+t*D at hh
  change (q.stk (.inl k)).length ≤ size+timePolynomial.eval size*D
  omega

namespace Fixtures
set_option maxRecDepth 4096 in
example : (runSteps machine.step 39 (cfg .scanVars none
    (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false]]) [true] [] [] [] [true,false,false,true])).map
    (fun q => (match q.l with | some (.inr (.inr (.inr .yes))) => true | _ => false,
      q.stk (.inr .vars),q.stk (.inr .witness),q.stk (.inr .scratch))) =
    some (true,Shared.ComplexityBridge.TM2WitnessLookup.frames [[false]],[true],[]) := by
  change (Option.map (fun q => (match q.l with | some (.inr (.inr (.inr .yes))) => true | _ => false,
      q.stk (.inr .vars),q.stk (.inr .witness),q.stk (.inr .scratch)))
    (runSteps machine.step 39 (cfg .scanVars none
      (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false]]) [true] [] [] [] [true,false,false,true])) :
        Option (Bool × List Bool × List Bool × List Bool)) = _
  decide

example : runSteps machine.step 5 (cfg .scanVars none [] [] [] [] [] []) =
    some (embed (extras [] [] []) (Shared.ComplexityBridge.TM2LiteralEval.loaded [] [] [])) := by
  simpa using copy_and_start [] [] []
end Fixtures

end Shared.ComplexityBridge.TM2LiteralPreserve
