import Shared.ComplexityBridge.TM2LiteralOutput
import Shared.ComplexityBridge.CNFFlattenBridge

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2LiteralStream
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Outer := Shared.ComplexityBridge.TM2Undelimit.machine
abbrev Literal := Shared.ComplexityBridge.TM2LiteralParse.machine
abbrev SKey := Shared.ComplexityBridge.TM2Undelimit.Stack
abbrev OuterLabel := Shared.ComplexityBridge.TM2Undelimit.Label
abbrev LiteralLabel := Shared.ComplexityBridge.TM2LiteralParse.Label
abbrev LiteralState := Shared.ComplexityBridge.TM2LiteralParse.State
inductive Key where | stream | literal | scratch | name | accum deriving DecidableEq
inductive Phase where | start | copy | good | bad deriving DecidableEq
instance : Fintype Key := Fintype.ofList [.stream,.literal,.scratch,.name,.accum] (by intro k; cases k <;> simp)
instance : Fintype Phase := Fintype.ofList [.start,.copy,.good,.bad] (by intro p; cases p <;> simp)
abbrev Label := Phase ⊕ (OuterLabel ⊕ LiteralLabel)
abbrev State := Option Bool ⊕ (LiteralState ⊕ Option Bool)
def outerState : State → Option Bool | .inl v => v | _ => none
def literalState : State → LiteralState | .inr (.inl v) => v | _ => Literal.initialState
def phaseState : State → Option Bool | .inr (.inr v) => v | _ => none

def keyMap (stage : Bool) : SKey → Key :=
  if stage then fun k => match k with | .input => .literal | .scratch => .scratch | .payload => .name
  else fun k => match k with | .input => .stream | .scratch => .scratch | .payload => .literal

def stackMap (stage : Bool) (S : SKey → List Bool) (other : Key → List Bool) : Key → List Bool :=
  if stage then fun k => match k with
    | .literal => S .input | .scratch => S .scratch | .name => S .payload | k => other k
  else fun k => match k with
    | .stream => S .input | .scratch => S .scratch | .literal => S .payload | k => other k

@[simp] theorem stackMap_apply (stage : Bool) (S : SKey → List Bool) (other : Key → List Bool) (j : SKey) :
    stackMap stage S other (keyMap stage j) = S j := by cases stage <;> cases j <;> rfl

theorem stackMap_update (stage : Bool) (S : SKey → List Bool) (other : Key → List Bool) (j : SKey) (xs : List Bool) :
    stackMap stage (Function.update S j xs) other = Function.update (stackMap stage S other) (keyMap stage j) xs := by
  funext k; cases stage <;> cases j <;> cases k <;> simp [stackMap,keyMap,Function.update]

def outerEmbed (other : Key → List Bool) (q : Outer.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map (fun l => .inr (.inl l)),.inl q.var,stackMap false q.stk other⟩
def literalEmbed (other : Key → List Bool) (q : Literal.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map (fun l => .inr (.inr l)),.inr (.inl q.var),stackMap true q.stk other⟩

def liftOuter : Stmt (fun _ : SKey => Bool) OuterLabel (Option Bool) → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push (keyMap false j) (fun v => f (outerState v)) (liftOuter q)
  | .peek j f q => .peek (keyMap false j) (fun v h => .inl (f (outerState v) h)) (liftOuter q)
  | .pop j f q => .pop (keyMap false j) (fun v h => .inl (f (outerState v) h)) (liftOuter q)
  | .load f q => .load (fun v => .inl (f (outerState v))) (liftOuter q)
  | .branch f q r => .branch (fun v => f (outerState v)) (liftOuter q) (liftOuter r)
  | .goto f => .goto (fun v => .inr (.inl (f (outerState v))))
  | .halt => .halt

def liftLiteral : Stmt (fun _ : SKey => Bool) LiteralLabel LiteralState → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push (keyMap true j) (fun v => f (literalState v)) (liftLiteral q)
  | .peek j f q => .peek (keyMap true j) (fun v h => .inr (.inl (f (literalState v) h))) (liftLiteral q)
  | .pop j f q => .pop (keyMap true j) (fun v h => .inr (.inl (f (literalState v) h))) (liftLiteral q)
  | .load f q => .load (fun v => .inr (.inl (f (literalState v)))) (liftLiteral q)
  | .branch f q r => .branch (fun v => f (literalState v)) (liftLiteral q) (liftLiteral r)
  | .goto f => .goto (fun v => .inr (.inr (f (literalState v))))
  | .halt => .halt

theorem liftOuter_aux (q : Outer.Stmt) (v : Option Bool) (S : SKey → List Bool) (other : Key → List Bool) :
    stepAux (liftOuter q) (.inl v) (stackMap false S other) = outerEmbed other (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih =>
    simp only [liftOuter,stepAux,outerState,stackMap_apply]
    rw [← stackMap_update false S other j (f v::S j)]; exact ih _ _
  | peek j f q ih => simp only [liftOuter,stepAux,outerState,stackMap_apply]; exact ih _ _
  | pop j f q ih =>
    simp only [liftOuter,stepAux,outerState,stackMap_apply]
    rw [← stackMap_update false S other j (S j).tail]; exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftOuter,stepAux,outerState,h,ihq,ihr]

theorem liftLiteral_aux (q : Literal.Stmt) (v : LiteralState) (S : SKey → List Bool) (other : Key → List Bool) :
    stepAux (liftLiteral q) (.inr (.inl v)) (stackMap true S other) = literalEmbed other (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih =>
    simp only [liftLiteral,stepAux,literalState,stackMap_apply]
    rw [← stackMap_update true S other j (f v::S j)]; exact ih _ _
  | peek j f q ih => simp only [liftLiteral,stepAux,literalState,stackMap_apply]; exact ih _ _
  | pop j f q ih =>
    simp only [liftLiteral,stepAux,literalState,stackMap_apply]
    rw [← stackMap_update true S other j (S j).tail]; exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftLiteral,stepAux,literalState,h,ihq,ihr]

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl .start => .peek .stream (fun _ h => .inr (.inr h))
      (.branch (fun v => (phaseState v).isSome)
        (.load (fun _ => .inl none) (.goto (fun _ => .inr (.inl .header))))
        (.goto (fun _ => .inl .good)))
  | .inl .copy => .pop .name (fun _ h => .inr (.inr h))
      (.branch (fun v => (phaseState v).isSome)
        (.push .accum (fun _ => true) (.push .accum (fun v => (phaseState v).getD false) (.goto (fun _ => .inl .copy))))
        (.push .accum (fun _ => false) (.goto (fun _ => .inl .start))))
  | .inl .good => .goto (fun _ => .inl .good)
  | .inl .bad => .goto (fun _ => .inl .bad)
  | .inr (.inl .done) => .load (fun _ => .inr (.inl Literal.initialState)) (.goto (fun _ => .inr (.inr Literal.main)))
  | .inr (.inl .reject) => .goto (fun _ => .inl .bad)
  | .inr (.inl l) => liftOuter (Shared.ComplexityBridge.TM2Undelimit.program l)
  | .inr (.inr (.inr .accept)) => .load (fun _ => .inr (.inr none)) (.goto (fun _ => .inl .copy))
  | .inr (.inr (.inr .reject)) => .goto (fun _ => .inl .bad)
  | .inr (.inr l) => liftLiteral (Shared.ComplexityBridge.TM2LiteralParse.program l)

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .stream
  k₁ := .accum
  Γ := fun _ => Bool
  Λ := Label
  main := .inl .start
  σ := State
  initialState := .inr (.inr none)
  m := program

def outerTerminal (q : Outer.Cfg) : Prop := q.l = some .done ∨ q.l = some .reject
noncomputable instance : DecidablePred outerTerminal := fun _ => Classical.propDecidable _
theorem outer_stable (q : Outer.Cfg) (h : outerTerminal q) : Outer.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2Undelimit.Label.done ∨ l = some Shared.ComplexityBridge.TM2Undelimit.Label.reject at h
    rcases h with h | h <;> subst l <;> rfl

theorem outer_step (other : Key → List Bool) (q : Outer.Cfg) (h : ¬ outerTerminal q) :
    machine.step (outerEmbed other q) = (Outer.step q).map (outerEmbed other) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | done => exact False.elim (h (Or.inl rfl))
      | reject => exact False.elim (h (Or.inr rfl))
      | header | data | restore =>
        change some (stepAux (liftOuter (Shared.ComplexityBridge.TM2Undelimit.program _)) (.inl v) (stackMap false S other)) = _
        rw [liftOuter_aux]; rfl

def literalTerminal (q : Literal.Cfg) : Prop := q.l = some (.inr .accept) ∨ q.l = some (.inr .reject)
noncomputable instance : DecidablePred literalTerminal := fun _ => Classical.propDecidable _
theorem literal_stable (q : Literal.Cfg) (h : literalTerminal q) : Literal.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some (.inr Shared.ComplexityBridge.TM2LiteralParse.CheckLabel.accept) ∨
      l = some (.inr Shared.ComplexityBridge.TM2LiteralParse.CheckLabel.reject) at h
    rcases h with h | h <;> subst l <;> rfl

theorem literal_step (other : Key → List Bool) (q : Literal.Cfg) (h : ¬ literalTerminal q) :
    machine.step (literalEmbed other q) = (Literal.step q).map (literalEmbed other) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | inl l =>
        change some (stepAux (liftLiteral (Shared.ComplexityBridge.TM2LiteralParse.program (.inl l))) (.inr (.inl v)) (stackMap true S other)) = _
        rw [liftLiteral_aux]; rfl
      | inr l => cases l with
        | accept => exact False.elim (h (Or.inl rfl))
        | reject => exact False.elim (h (Or.inr rfl))
        | sign | endSign =>
          change some (stepAux (liftLiteral (Shared.ComplexityBridge.TM2LiteralParse.program _)) (.inr (.inl v)) (stackMap true S other)) = _
          rw [liftLiteral_aux]; rfl

def stackVals (stream literal scratch name accum : List Bool) : Key → List Bool
  | .stream => stream | .literal => literal | .scratch => scratch | .name => name | .accum => accum

def cfg (l : Phase) (flag : Option Bool) (stream literal scratch name accum : List Bool) : machine.Cfg :=
  ⟨some (.inl l),.inr (.inr flag),stackVals stream literal scratch name accum⟩

theorem initial_eq (input : List Bool) : Turing.initList machine input = cfg .start none input [] [] [] [] := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1; funext k; cases k <;> simp [machine,stackVals,Turing.initList] <;> rfl

theorem start_nil (flag : Option Bool) (accum : List Bool) :
    machine.step (cfg .start flag [] [] [] [] accum) = some (cfg .good none [] [] [] [] accum) := by rfl

theorem start_cons (flag : Option Bool) (b : Bool) (tail accum : List Bool) :
    machine.step (cfg .start flag (b::tail) [] [] [] accum) =
      some (outerEmbed (stackVals [] [] [] [] accum) (Turing.initList Outer (b::tail))) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [outerEmbed,stackMap,stackVals,Turing.initList,Outer,Shared.ComplexityBridge.TM2Undelimit.machine] <;> rfl

theorem outer_done (tail payload accum : List Bool) :
    machine.step (outerEmbed (stackVals [] [] [] [] accum) (Shared.ComplexityBridge.TM2Undelimit.cfg .done none tail [] payload)) =
      some (literalEmbed (stackVals tail [] [] [] accum) (Turing.initList Literal payload)) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> simp [outerEmbed,literalEmbed,stackMap,stackVals,
    Shared.ComplexityBridge.TM2Undelimit.cfg,Shared.ComplexityBridge.TM2Undelimit.stackVals,Turing.initList,Literal,
    Shared.ComplexityBridge.TM2LiteralParse.machine] <;> rfl

theorem literal_accept (tail name accum : List Bool) (sign : Bool) :
    machine.step (literalEmbed (stackVals tail [] [] [] accum) (Shared.ComplexityBridge.TM2LiteralParse.cfg .accept (some sign) none [] [] name)) =
      some (cfg .copy none tail [] [] name accum) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;> rfl

theorem copy_cons (flag : Option Bool) (b : Bool) (tail name accum : List Bool) :
    machine.step (cfg .copy flag tail [] [] (b::name) accum) = some (cfg .copy (some b) tail [] [] name (b::true::accum)) := by
  change some (Cfg.mk _ _ (Function.update (Function.update (Function.update
    (stackVals tail [] [] (b::name) accum) .name name) .accum (true::accum)) .accum (b::true::accum))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem copy_nil (flag : Option Bool) (tail accum : List Bool) :
    machine.step (cfg .copy flag tail [] [] [] accum) = some (cfg .start none tail [] [] [] (false::accum)) := by
  change some (Cfg.mk _ _ (Function.update (Function.update (stackVals tail [] [] [] accum) .name []) .accum (false::accum))) = _
  congr 1; congr 1; funext k; cases k <;> simp [stackVals,Function.update]

theorem copy_frame (name tail accum : List Bool) (flag : Option Bool) :
    runSteps machine.step (name.length+1) (cfg .copy flag tail [] [] name accum) =
      some (cfg .start none tail [] [] [] ((BitstringEncoding.delimit name).reverse++accum)) := by
  induction name generalizing flag accum with
  | nil =>
    change machine.step (cfg .copy flag tail [] [] [] accum) = _
    simpa [BitstringEncoding.delimit] using copy_nil flag tail accum
  | cons b name ih =>
    rw [List.length_cons,show name.length+1+1 = (name.length+1)+1 by omega,runSteps_front,copy_cons]
    simpa [BitstringEncoding.delimit,List.reverse_cons,List.append_assoc] using ih (b::true::accum) (some b)

theorem start_delimit (payload tail accum : List Bool) (flag : Option Bool) :
    machine.step (cfg .start flag (BitstringEncoding.delimit payload ++ tail) [] [] [] accum) =
      some (outerEmbed (stackVals [] [] [] [] accum) (Turing.initList Outer (BitstringEncoding.delimit payload ++ tail))) := by
  cases payload with
  | nil => exact start_cons flag false tail accum
  | cons b payload => exact start_cons flag true (b::BitstringEncoding.delimit payload ++ tail) accum

theorem outer_rejected (q : Outer.Cfg) (other : Key → List Bool) (h : q.l = some .reject) :
    ∃ r, machine.step (outerEmbed other q) = some r ∧ r.l = some (.inl .bad) := by
  cases q with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2Undelimit.Label.reject at h
    subst l
    refine ⟨⟨some (.inl .bad),.inl v,stackMap false S other⟩,rfl,rfl⟩

theorem literal_rejected (q : Literal.Cfg) (other : Key → List Bool) (h : q.l = some (.inr .reject)) :
    ∃ r, machine.step (literalEmbed other q) = some r ∧ r.l = some (.inl .bad) := by
  cases q with
  | mk l v S =>
    change l = some (.inr Shared.ComplexityBridge.TM2LiteralParse.CheckLabel.reject) at h
    subst l
    refine ⟨⟨some (.inl .bad),.inr (.inl v),stackMap true S other⟩,rfl,rfl⟩

/-- One well-formed occurrence consumes exactly one framed literal and appends
its raw variable name to the reverse accumulator. -/
theorem process_one (payload tail name accum : List Bool) (sign : Bool) (flag : Option Bool)
    (hname : Shared.ComplexityBridge.TM2LiteralParse.literalBits payload = some (name,sign)) :
    ∃ t ≤ 7*(BitstringEncoding.delimit payload ++ tail).length+11,
      runSteps machine.step t (cfg .start flag (BitstringEncoding.delimit payload ++ tail) [] [] [] accum) =
        some (cfg .start none tail [] [] [] ((BitstringEncoding.delimit name).reverse++accum)) := by
  let bits := BitstringEncoding.delimit payload ++ tail
  let outerOther := stackVals [] [] [] [] accum
  let outerEnd := Shared.ComplexityBridge.TM2Undelimit.cfg .done none tail [] payload
  let litOther := stackVals tail [] [] [] accum
  let litEnd := Shared.ComplexityBridge.TM2LiteralParse.cfg .accept (some sign) none [] [] name
  have hp := Shared.ComplexityBridge.TM2Undelimit.valid_run payload tail
  change runSteps Outer.step (3*payload.length+2) (Turing.initList Outer bits) = some outerEnd at hp
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Outer.step machine.step (outerEmbed outerOther) outerTerminal outer_stable (outer_step outerOther)
    _ (Turing.initList Outer bits) outerEnd (Or.inl rfl) hp
  obtain ⟨n,hn,q,hr,hq⟩ := Shared.ComplexityBridge.TM2LiteralParse.parse_progress payload
  have hq' : q = litEnd := by simpa [hname] using hq
  subst q
  change runSteps Literal.step n (Turing.initList Literal payload) = some litEnd at hr
  obtain ⟨b,hb,hbr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Literal.step machine.step (literalEmbed litOther) literalTerminal literal_stable (literal_step litOther)
    n (Turing.initList Literal payload) litEnd (Or.inl rfl) hr
  have hpayload : name.length ≤ payload.length := by
    unfold Shared.ComplexityBridge.TM2LiteralParse.literalBits at hname
    cases hd : BitstringEncoding.undelimit payload with
    | none => simp [hd] at hname
    | some p =>
      rcases p with ⟨v,rest⟩
      cases rest with
      | nil => simp [hd] at hname
      | cons z rest => cases rest with
        | cons d rest => simp [hd] at hname
        | nil =>
          simp [hd] at hname
          have hv : v = name := hname.1
          subst v
          have he := Shared.ComplexityBridge.CNFWitness.undelimit_sound payload name [z] hd
          have hl := congrArg List.length he
          simp only [List.length_append,BitstringEncoding.length_delimit,List.length_cons,List.length_nil] at hl
          omega
  have hbits : bits.length = 2*payload.length+1+tail.length := by simp [bits,BitstringEncoding.length_delimit]
  refine ⟨1+a+1+b+1+(name.length+1),?_,?_⟩
  · change 1+a+1+b+1+(name.length+1) ≤ 7*bits.length+11
    omega
  · rw [show 1+a+1+b+1+(name.length+1) = 1+(a+(1+(b+(1+(name.length+1))))) by omega,runSteps_add]
    change (machine.step (cfg .start flag bits [] [] [] accum)).bind _ = _
    rw [start_delimit]
    change runSteps machine.step (a+(1+(b+(1+(name.length+1))))) (outerEmbed outerOther (Turing.initList Outer bits)) = _
    rw [runSteps_add,har]
    change runSteps machine.step (1+(b+(1+(name.length+1)))) (outerEmbed outerOther outerEnd) = _
    rw [runSteps_add]
    change (machine.step (outerEmbed outerOther outerEnd)).bind _ = _
    rw [outer_done]
    change runSteps machine.step (b+(1+(name.length+1))) (literalEmbed litOther (Turing.initList Literal payload)) = _
    rw [runSteps_add,hbr]
    change runSteps machine.step (1+(name.length+1)) (literalEmbed litOther litEnd) = _
    rw [runSteps_add]
    change (machine.step (literalEmbed litOther litEnd)).bind _ = _
    rw [literal_accept]
    exact copy_frame name tail accum none

/-- An incomplete outer frame reaches the bad continuation in finite time. -/
theorem bad_outer (input accum : List Bool) (flag : Option Bool) (hne : input ≠ [])
    (hbad : BitstringEncoding.undelimit input = none) :
    ∃ t ≤ input.length+3, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start flag input [] [] [] accum) = some q ∧ q.l = some (.inl .bad) := by
  obtain ⟨n,hn,scratch,hr⟩ := Shared.ComplexityBridge.TM2Undelimit.invalid_run input [] [] none hbad
  rw [← Shared.ComplexityBridge.TM2Undelimit.initial_eq] at hr
  let other := stackVals [] [] [] [] accum
  let finish := Shared.ComplexityBridge.TM2Undelimit.cfg .reject none [] scratch []
  change runSteps Outer.step n (Turing.initList Outer input) = some finish at hr
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Outer.step machine.step (outerEmbed other) outerTerminal outer_stable (outer_step other)
    n (Turing.initList Outer input) finish (Or.inr rfl) hr
  obtain ⟨r,hs,hl⟩ := outer_rejected finish other rfl
  refine ⟨1+a+1,by omega,r,?_,hl⟩
  cases input with
  | nil => exact False.elim (hne rfl)
  | cons x xs =>
    rw [show 1+a+1 = 1+(a+1) by omega,runSteps_add]
    change (machine.step (cfg .start flag (x::xs) [] [] [] accum)).bind _ = _
    rw [start_cons]
    change runSteps machine.step (a+1) (outerEmbed other (Turing.initList Outer (x::xs))) = _
    rw [runSteps_add,har]
    exact hs

/-- A well-framed but malformed literal reaches the bad continuation. -/
theorem bad_literal (payload tail accum : List Bool) (flag : Option Bool)
    (hbad : Shared.ComplexityBridge.TM2LiteralParse.literalBits payload = none) :
    ∃ t ≤ 7*(BitstringEncoding.delimit payload ++ tail).length+11, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start flag (BitstringEncoding.delimit payload ++ tail) [] [] [] accum) = some q ∧
        q.l = some (.inl .bad) := by
  let bits := BitstringEncoding.delimit payload ++ tail
  let outerOther := stackVals [] [] [] [] accum
  let outerEnd := Shared.ComplexityBridge.TM2Undelimit.cfg .done none tail [] payload
  let litOther := stackVals tail [] [] [] accum
  have hp := Shared.ComplexityBridge.TM2Undelimit.valid_run payload tail
  change runSteps Outer.step (3*payload.length+2) (Turing.initList Outer bits) = some outerEnd at hp
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Outer.step machine.step (outerEmbed outerOther) outerTerminal outer_stable (outer_step outerOther)
    _ (Turing.initList Outer bits) outerEnd (Or.inl rfl) hp
  obtain ⟨n,hn,q,hr,hq⟩ := Shared.ComplexityBridge.TM2LiteralParse.parse_progress payload
  have hq' : q.l = some (.inr .reject) := by simpa [hbad] using hq
  change runSteps Literal.step n (Turing.initList Literal payload) = some q at hr
  obtain ⟨b,hb,hbr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Literal.step machine.step (literalEmbed litOther) literalTerminal literal_stable (literal_step litOther)
    n (Turing.initList Literal payload) q (Or.inr hq') hr
  obtain ⟨r,hs,hl⟩ := literal_rejected q litOther hq'
  have hbits : bits.length = 2*payload.length+1+tail.length := by simp [bits,BitstringEncoding.length_delimit]
  refine ⟨1+a+1+b+1,?_,r,?_,hl⟩
  · change 1+a+1+b+1 ≤ 7*bits.length+11
    omega
  · rw [show 1+a+1+b+1 = 1+(a+(1+(b+1))) by omega,runSteps_add]
    change (machine.step (cfg .start flag bits [] [] [] accum)).bind _ = _
    rw [start_delimit]
    change runSteps machine.step (a+(1+(b+1))) (outerEmbed outerOther (Turing.initList Outer bits)) = _
    rw [runSteps_add,har]
    change runSteps machine.step (1+(b+1)) (outerEmbed outerOther outerEnd) = _
    rw [runSteps_add]
    change (machine.step (outerEmbed outerOther outerEnd)).bind _ = _
    rw [outer_done]
    change runSteps machine.step (b+1) (literalEmbed litOther (Turing.initList Literal payload)) = _
    rw [runSteps_add,hbr]
    exact hs

/-- Parse every framed literal, preserving the original variable-name bits.
The recursion consumes at least one input bit per completed frame. -/
def parseNames (input : List Bool) : Option (List (List Bool)) :=
  if input = [] then some [] else
    match h : BitstringEncoding.undelimit input with
    | none => none
    | some (payload,tail) =>
      match Shared.ComplexityBridge.TM2LiteralParse.literalBits payload with
      | none => none
      | some (name,_) => (parseNames tail).map (name::·)
termination_by input.length
decreasing_by
  have hh := Shared.ComplexityBridge.CNFWitness.undelimit_sound input payload tail h
  have hl := congrArg List.length hh
  simp only [List.length_append,BitstringEncoding.length_delimit] at hl
  omega

theorem parseNames_nil : parseNames [] = some [] := by rw [parseNames]; rfl

theorem parseNames_bad_frame (x : Bool) (xs : List Bool)
    (h : BitstringEncoding.undelimit (x::xs) = none) : parseNames (x::xs) = none := by
  rw [parseNames]
  simp only [List.cons_ne_nil,if_false]
  split <;> simp_all

theorem parseNames_bad_literal (x : Bool) (xs payload tail : List Bool)
    (h : BitstringEncoding.undelimit (x::xs) = some (payload,tail))
    (hl : Shared.ComplexityBridge.TM2LiteralParse.literalBits payload = none) : parseNames (x::xs) = none := by
  rw [parseNames]
  simp only [List.cons_ne_nil,if_false]
  split <;> simp_all

theorem parseNames_good_literal (x : Bool) (xs payload tail name : List Bool) (sign : Bool)
    (h : BitstringEncoding.undelimit (x::xs) = some (payload,tail))
    (hl : Shared.ComplexityBridge.TM2LiteralParse.literalBits payload = some (name,sign)) :
    parseNames (x::xs) = (parseNames tail).map (name::·) := by
  rw [parseNames]
  simp only [List.cons_ne_nil,if_false]
  split <;> simp_all

/-- Every raw occurrence stream reaches success with the exact framed names,
or reaches failure. The bound covers arbitrarily many parser invocations. -/
theorem stream_run (input accum : List Bool) (flag : Option Bool) :
    ∃ t ≤ input.length*(7*input.length+11)+1, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start flag input [] [] [] accum) = some q ∧
      match parseNames input with
      | none => q.l = some (.inl .bad)
      | some names => q = cfg .good none [] [] [] [] ((Shared.ComplexityBridge.TM2WitnessLookup.frames names).reverse++accum) := by
  cases input with
  | nil =>
    refine ⟨1,by simp,cfg .good none [] [] [] [] accum,?_,?_⟩
    · exact start_nil flag accum
    · simp [parseNames_nil,Shared.ComplexityBridge.TM2WitnessLookup.frames]
  | cons x xs =>
    let raw := x::xs
    cases hframe : BitstringEncoding.undelimit raw with
    | none =>
      obtain ⟨t,ht,q,hr,hq⟩ := bad_outer raw accum flag (by simp [raw]) hframe
      refine ⟨t,?_,q,hr,?_⟩
      · have hn : 1 ≤ raw.length := by simp [raw]
        have hm := Nat.mul_le_mul_right (7*raw.length+11) hn
        change t ≤ raw.length*(7*raw.length+11)+1
        omega
      · change (match parseNames (x::xs) with | none => _ | some _ => _)
        rw [parseNames_bad_frame x xs hframe]
        exact hq
    | some p =>
      rcases p with ⟨payload,tail⟩
      have he := Shared.ComplexityBridge.CNFWitness.undelimit_sound raw payload tail hframe
      have hl : raw.length = 2*payload.length+1+tail.length := by
        rw [← he,List.length_append,BitstringEncoding.length_delimit]
      have hlt : tail.length < raw.length := by omega
      cases hname : Shared.ComplexityBridge.TM2LiteralParse.literalBits payload with
      | none =>
        obtain ⟨t,ht,q,hr,hq⟩ := bad_literal payload tail accum flag hname
        have ht' : t ≤ 7*raw.length+11 := by simpa [he] using ht
        refine ⟨t,?_,q,?_,?_⟩
        · have hn : 1 ≤ raw.length := by simp [raw]
          have hm := Nat.mul_le_mul_right (7*raw.length+11) hn
          change t ≤ raw.length*(7*raw.length+11)+1
          omega
        · simpa [he] using hr
        · change (match parseNames (x::xs) with | none => _ | some _ => _)
          rw [parseNames_bad_literal x xs payload tail hframe hname]
          exact hq
      | some pair =>
        rcases pair with ⟨name,sign⟩
        obtain ⟨a,ha,har⟩ := process_one payload tail name accum sign flag hname
        have ha' : a ≤ 7*raw.length+11 := by simpa [he] using ha
        obtain ⟨b,hb,q,hbr,hq⟩ := stream_run tail ((BitstringEncoding.delimit name).reverse++accum) none
        have hmul1 := Nat.mul_le_mul_left tail.length (show 7*tail.length+11 ≤ 7*raw.length+11 by omega)
        have hmul2 := Nat.mul_le_mul_right (7*raw.length+11) (show tail.length+1 ≤ raw.length by omega)
        have hadd : (tail.length+1)*(7*raw.length+11) = tail.length*(7*raw.length+11)+(7*raw.length+11) := by simp [Nat.add_mul]
        refine ⟨a+b,?_,q,?_,?_⟩
        · change a+b ≤ raw.length*(7*raw.length+11)+1
          omega
        · change runSteps machine.step (a+b) (cfg .start flag raw [] [] [] accum) = _
          rw [runSteps_add,← he,har]
          exact hbr
        · cases hn : parseNames tail with
          | none =>
            have hbq : q.l = some (.inl .bad) := by simpa [hn] using hq
            change (match parseNames (x::xs) with | none => _ | some _ => _)
            rw [parseNames_good_literal x xs payload tail name sign hframe hname,hn]
            exact hbq
          | some names =>
            have hbq : q = cfg .good none [] [] [] [] ((Shared.ComplexityBridge.TM2WitnessLookup.frames names).reverse ++ (BitstringEncoding.delimit name).reverse ++ accum) := by
              simpa [hn,List.append_assoc] using hq
            change (match parseNames (x::xs) with | none => _ | some _ => _)
            rw [parseNames_good_literal x xs payload tail name sign hframe hname,hn]
            simpa [Shared.ComplexityBridge.TM2WitnessLookup.frames_cons,List.reverse_append,List.append_assoc] using hbq
termination_by input.length
decreasing_by exact hlt

theorem parseNames_frame (payload tail : List Bool) :
    parseNames (BitstringEncoding.delimit payload ++ tail) =
      match Shared.ComplexityBridge.TM2LiteralParse.literalBits payload with
      | none => none
      | some (name,_) => (parseNames tail).map (name::·) := by
  have hp := BitstringEncoding.undelimit_delimit payload tail
  cases hl : Shared.ComplexityBridge.TM2LiteralParse.literalBits payload with
  | none =>
    cases payload with
    | nil => exact parseNames_bad_literal false tail [] tail hp hl
    | cons b payload => exact parseNames_bad_literal true (b::BitstringEncoding.delimit payload ++ tail) (b::payload) tail hp hl
  | some p =>
    rcases p with ⟨name,sign⟩
    cases payload with
    | nil => exact parseNames_good_literal false tail [] tail name sign hp hl
    | cons b payload => exact parseNames_good_literal true (b::BitstringEncoding.delimit payload ++ tail) (b::payload) tail name sign hp hl

/-- On valid outer framing, the loop specification is elementwise literal
parsing with signs projected away. -/
theorem parseNames_framed (literals : List (List Bool)) :
    parseNames (Shared.ComplexityBridge.TM2WitnessLookup.frames literals) =
      (literals.mapM Shared.ComplexityBridge.TM2LiteralParse.literalBits).map (List.map Prod.fst) := by
  induction literals with
  | nil => simpa [Shared.ComplexityBridge.TM2WitnessLookup.frames] using parseNames_nil
  | cons lit literals ih =>
    rw [Shared.ComplexityBridge.TM2WitnessLookup.frames_cons,parseNames_frame]
    cases hl : Shared.ComplexityBridge.TM2LiteralParse.literalBits lit with
    | none => simp [hl,List.mapM_cons]
    | some p =>
      rcases p with ⟨name,sign⟩
      simp only [hl,List.mapM_cons,Option.bind_some]
      rw [ih]
      cases literals.mapM Shared.ComplexityBridge.TM2LiteralParse.literalBits <;> rfl

/-- If outer block parsing fails, the occurrence parser cannot report success. -/
theorem parseNames_bad_blocks (input : List Bool) (hbad : BitstringEncoding.undelimitBlocks input = none) :
    parseNames input = none := by
  cases input with
  | nil => simp [BitstringEncoding.undelimitBlocks,BitstringEncoding.undelimitBlocksAux] at hbad
  | cons x xs =>
    cases ho : BitstringEncoding.undelimit (x::xs) with
    | none => exact parseNames_bad_frame x xs ho
    | some p =>
      rcases p with ⟨payload,tail⟩
      have he := Shared.ComplexityBridge.CNFWitness.undelimit_sound (x::xs) payload tail ho
      have htail : BitstringEncoding.undelimitBlocks tail = none := by
        cases ht : BitstringEncoding.undelimitBlocks tail with
        | none => rfl
        | some blocks =>
          have hblocks := Shared.ComplexityBridge.CNFWitness.blocks_sound tail blocks ht
          have hfull : Shared.ComplexityBridge.TM2WitnessLookup.frames (payload::blocks) = x::xs := by
            rw [Shared.ComplexityBridge.TM2WitnessLookup.frames_cons]
            change BitstringEncoding.delimit payload ++ (blocks.map BitstringEncoding.delimit).flatten = x::xs
            rw [hblocks]
            exact he
          have hv := BitstringEncoding.undelimitBlocks_flatten_delimit (payload::blocks)
          change BitstringEncoding.undelimitBlocks (Shared.ComplexityBridge.TM2WitnessLookup.frames (payload::blocks)) = _ at hv
          rw [hfull,hbad] at hv
          contradiction
      have hlt : tail.length < (x::xs).length := by
        have hl := congrArg List.length he
        simp only [List.length_append,BitstringEncoding.length_delimit,List.length_cons] at hl
        simp only [List.length_cons]
        omega
      cases hn : Shared.ComplexityBridge.TM2LiteralParse.literalBits payload with
      | none => exact parseNames_bad_literal x xs payload tail ho hn
      | some p =>
        rcases p with ⟨name,sign⟩
        rw [parseNames_good_literal x xs payload tail name sign ho hn,parseNames_bad_blocks tail htail]
        rfl
termination_by input.length

/-- The operational specification agrees for every bitstring with the pinned
block parser followed by literal parsing and name projection. -/
theorem parseNames_correct (input : List Bool) :
    parseNames input = (BitstringEncoding.undelimitBlocks input).bind
      (fun lits => (lits.mapM Shared.ComplexityBridge.TM2LiteralParse.literalBits).map (List.map Prod.fst)) := by
  cases h : BitstringEncoding.undelimitBlocks input with
  | none => simpa [h] using parseNames_bad_blocks input h
  | some lits =>
    have he := Shared.ComplexityBridge.CNFWitness.blocks_sound input lits h
    change Shared.ComplexityBridge.TM2WitnessLookup.frames lits = input at he
    rw [← he,parseNames_framed]
    simp [h,he]

/-- Starting from the designated input configuration, the finite machine
implements the total occurrence specification and returns reverse-framed names
at the success continuation. -/
theorem parse_progress (input : List Bool) :
    ∃ t ≤ input.length*(7*input.length+11)+1, ∃ q : machine.Cfg,
      runSteps machine.step t (Turing.initList machine input) = some q ∧
      match parseNames input with
      | none => q.l = some (.inl .bad)
      | some names => q = cfg .good none [] [] [] [] (Shared.ComplexityBridge.TM2WitnessLookup.frames names).reverse := by
  obtain ⟨t,ht,q,hr,hq⟩ := stream_run input [] none
  refine ⟨t,ht,q,?_,?_⟩
  · simpa [initial_eq] using hr
  · cases h : parseNames input <;> simpa [h] using hq

/-- Successful CNF decoding supplies a literal stream whose finite extractor
produces the verifier's variable occurrences, even for noncanonical numerals. -/
theorem cnf_occurrence_progress (input : List Bool) (formula : Shared.ComplexityBridge.CNF.Formula)
    (h : Shared.ComplexityBridge.CNF.parse input = some formula) :
    ∃ literalStream names : List Bool, ∃ rawNames : List (List Bool),
      Shared.ComplexityBridge.TM2FlattenBlocksTotal.decodeResult input = true::literalStream ∧
      names = Shared.ComplexityBridge.TM2WitnessLookup.frames rawNames ∧
      rawNames.map Computability.decodeNat = Shared.ComplexityBridge.CNF.variableOccurrences formula ∧
      ∃ t ≤ literalStream.length*(7*literalStream.length+11)+1,
        runSteps machine.step t (Turing.initList machine literalStream) =
          some (cfg .good none [] [] [] [] names.reverse) := by
  obtain ⟨clauses,groups,pairs,hc,hg,hn,hvars,hflat⟩ :=
    Shared.ComplexityBridge.CNFFlattenBridge.parse_occurrences_correct input formula h
  let literalStream := Shared.ComplexityBridge.TM2WitnessLookup.frames groups.flatten
  let rawNames := pairs.map Prod.fst
  have hp : parseNames literalStream = some rawNames := by
    dsimp [literalStream,rawNames]
    rw [parseNames_framed,hn]
    rfl
  obtain ⟨t,ht,q,hr,hq⟩ := parse_progress literalStream
  have hq' : q = cfg .good none [] [] [] [] (Shared.ComplexityBridge.TM2WitnessLookup.frames rawNames).reverse := by simpa [hp] using hq
  refine ⟨literalStream,Shared.ComplexityBridge.TM2WitnessLookup.frames rawNames,rawNames,hflat,rfl,hvars,t,ht,?_⟩
  simpa [hq'] using hr

namespace Fixtures
example : (runSteps machine.step 18 (Turing.initList machine
    (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false,true]]))).map
    (fun q => ((match q.l with | some (.inl .good) => true | _ => false),q.stk .accum)) = some (true,[false]) := by
  rw [initial_eq]
  change (Option.map (fun q => ((match q.l with | some (.inl .good) => true | _ => false),q.stk .accum))
    (runSteps machine.step 18 (cfg .start none (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false,true]]) [] [] [] [])) : Option (Bool × List Bool)) = _
  decide
set_option maxRecDepth 4096 in
example : (runSteps machine.step 45 (Turing.initList machine
    (Shared.ComplexityBridge.TM2WitnessLookup.frames [[true,false,false,true],[false,false]]))).map
    (fun q => ((match q.l with | some (.inl .good) => true | _ => false),q.stk .accum)) = some (true,[false,false,false,true]) := by
  rw [initial_eq]
  change (Option.map (fun q => ((match q.l with | some (.inl .good) => true | _ => false),q.stk .accum))
    (runSteps machine.step 45 (cfg .start none
      (Shared.ComplexityBridge.TM2WitnessLookup.frames [[true,false,false,true],[false,false]]) [] [] [] [])) : Option (Bool × List Bool)) = _
  decide
example : (runSteps machine.step 4 (Turing.initList machine [true])).map
    (fun q => match q.l with | some (.inl .bad) => true | _ => false) = some true := by
  rw [initial_eq]
  change (Option.map (fun q => match q.l with | some (.inl .bad) => true | _ => false)
    (runSteps machine.step 4 (cfg .start none [true] [] [] [] [])) : Option Bool) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2LiteralStream
