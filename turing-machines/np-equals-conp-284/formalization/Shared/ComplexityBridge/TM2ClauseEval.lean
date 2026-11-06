import Shared.ComplexityBridge.TM2LiteralClean
import Shared.ComplexityBridge.RawCNFEval

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2ClauseEval
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Outer := Shared.ComplexityBridge.TM2Undelimit.machine
abbrev Inner := Shared.ComplexityBridge.TM2LiteralClean.machine
abbrev OKey := Shared.ComplexityBridge.TM2Undelimit.Stack
abbrev IKey := Shared.ComplexityBridge.TM2LiteralClean.Key
abbrev OLabel := Shared.ComplexityBridge.TM2Undelimit.Label
abbrev ILabel := Shared.ComplexityBridge.TM2LiteralClean.Label
abbrev IState := Shared.ComplexityBridge.TM2LiteralClean.State
inductive Extra where | stream | scratch deriving DecidableEq
inductive Phase where | start | yes | no | invalid deriving DecidableEq
instance : Fintype Extra := Fintype.ofList [.stream,.scratch] (by intro k; cases k <;> simp)
instance : Fintype Phase := Fintype.ofList [.start,.yes,.no,.invalid] (by intro k; cases k <;> simp)
abbrev Key := IKey ⊕ Extra
abbrev Label := Phase ⊕ (OLabel ⊕ ILabel)
abbrev State := Bool × (Option Bool ⊕ (IState ⊕ Option Bool))
def outerState : State → Option Bool | (_, .inl v) => v | _ => none
def innerState : State → IState | (_, .inr (.inl v)) => v | _ => Inner.initialState
def flagState : State → Option Bool | (_, .inr (.inr v)) => v | _ => none
def accum (v : State) : Bool := v.1

def okey : OKey → Key | .input => .inr .stream | .scratch => .inr .scratch | .payload => .inl (.inl .left)
def ostacks (S : OKey → List Bool) (other : Key → List Bool) : Key → List Bool
  | .inr .stream => S .input | .inr .scratch => S .scratch | .inl (.inl .left) => S .payload | k => other k
def istacks (S : IKey → List Bool) (other : Key → List Bool) : Key → List Bool
  | .inl k => S k | .inr k => other (.inr k)
@[simp] theorem ostacks_apply (S : OKey → List Bool) (other : Key → List Bool) (k : OKey) : ostacks S other (okey k) = S k := by cases k <;> rfl
@[simp] theorem istacks_apply (S : IKey → List Bool) (other : Key → List Bool) (k : IKey) : istacks S other (.inl k) = S k := rfl

theorem oupdate (S : OKey → List Bool) (other : Key → List Bool) (j : OKey) (xs : List Bool) :
    ostacks (Function.update S j xs) other = Function.update (ostacks S other) (okey j) xs := by
  funext k; cases j <;> cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [ostacks,okey,Function.update] <;> rfl
    | inr k => cases k <;> simp [ostacks,okey,Function.update] <;> rfl
  | inr k => cases k <;> simp [ostacks,okey,Function.update] <;> rfl

theorem iupdate (S : IKey → List Bool) (other : Key → List Bool) (j : IKey) (xs : List Bool) :
    istacks (Function.update S j xs) other = Function.update (istacks S other) (.inl j) xs := by
  funext k; cases k with
  | inl k => by_cases h : k = j <;> simp [istacks,Function.update,h]
  | inr k => simp [istacks,Function.update]

def outerEmbed (a : Bool) (other : Key → List Bool) (q : Outer.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map (fun l => .inr (.inl l)),(a,.inl q.var),ostacks q.stk other⟩
def innerEmbed (a : Bool) (other : Key → List Bool) (q : Inner.Cfg) : Cfg (fun _ : Key => Bool) Label State :=
  ⟨q.l.map (fun l => .inr (.inr l)),(a,.inr (.inl q.var)),istacks q.stk other⟩

def liftOuter : Stmt (fun _ : OKey => Bool) OLabel (Option Bool) → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push (okey j) (fun v => f (outerState v)) (liftOuter q)
  | .peek j f q => .peek (okey j) (fun v h => (accum v,.inl (f (outerState v) h))) (liftOuter q)
  | .pop j f q => .pop (okey j) (fun v h => (accum v,.inl (f (outerState v) h))) (liftOuter q)
  | .load f q => .load (fun v => (accum v,.inl (f (outerState v)))) (liftOuter q)
  | .branch f q r => .branch (fun v => f (outerState v)) (liftOuter q) (liftOuter r)
  | .goto f => .goto (fun v => .inr (.inl (f (outerState v))))
  | .halt => .halt

def liftInner : Stmt (fun _ : IKey => Bool) ILabel IState → Stmt (fun _ : Key => Bool) Label State
  | .push j f q => .push (.inl j) (fun v => f (innerState v)) (liftInner q)
  | .peek j f q => .peek (.inl j) (fun v h => (accum v,.inr (.inl (f (innerState v) h)))) (liftInner q)
  | .pop j f q => .pop (.inl j) (fun v h => (accum v,.inr (.inl (f (innerState v) h)))) (liftInner q)
  | .load f q => .load (fun v => (accum v,.inr (.inl (f (innerState v))))) (liftInner q)
  | .branch f q r => .branch (fun v => f (innerState v)) (liftInner q) (liftInner r)
  | .goto f => .goto (fun v => .inr (.inr (f (innerState v))))
  | .halt => .halt

theorem liftOuter_aux (q : Outer.Stmt) (a : Bool) (v : Option Bool) (S : OKey → List Bool) (other : Key → List Bool) :
    stepAux (liftOuter q) (a,.inl v) (ostacks S other) = outerEmbed a other (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih => simp only [liftOuter,stepAux,outerState,ostacks_apply]; rw [← oupdate S other j (f v::S j)]; exact ih _ _
  | peek j f q ih => simp only [liftOuter,stepAux,outerState,accum,ostacks_apply]; exact ih _ _
  | pop j f q ih => simp only [liftOuter,stepAux,outerState,accum,ostacks_apply]; rw [← oupdate S other j (S j).tail]; exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftOuter,stepAux,outerState,h,ihq,ihr]

theorem liftInner_aux (q : Inner.Stmt) (a : Bool) (v : IState) (S : IKey → List Bool) (other : Key → List Bool) :
    stepAux (liftInner q) (a,.inr (.inl v)) (istacks S other) = innerEmbed a other (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih => simp only [liftInner,stepAux,innerState,istacks_apply]; rw [← iupdate S other j (f v::S j)]; exact ih _ _
  | peek j f q ih => simp only [liftInner,stepAux,innerState,accum,istacks_apply]; exact ih _ _
  | pop j f q ih => simp only [liftInner,stepAux,innerState,accum,istacks_apply]; rw [← iupdate S other j (S j).tail]; exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftInner,stepAux,innerState,h,ihq,ihr]

def program : Label → Stmt (fun _ : Key => Bool) Label State
  | .inl .start => .peek (.inr .stream) (fun v h => (accum v,.inr (.inr h)))
      (.branch (fun v => (flagState v).isSome)
        (.load (fun v => (accum v,.inl none)) (.goto (fun _ => .inr (.inl .header))))
        (.branch accum (.goto (fun _ => .inl .yes)) (.goto (fun _ => .inl .no))))
  | .inl p => .goto (fun _ => .inl p)
  | .inr (.inl .done) => .load (fun v => (accum v,.inr (.inl Inner.initialState))) (.goto (fun _ => .inr (.inr Inner.main)))
  | .inr (.inl .reject) => .goto (fun _ => .inl .invalid)
  | .inr (.inr (.inr (.inr .invalid))) => .goto (fun _ => .inl .invalid)
  | .inr (.inr (.inr (.inr .yes))) => .load (fun _ => (true,.inr (.inr none))) (.goto (fun _ => .inl .start))
  | .inr (.inr (.inr (.inr .no))) => .load (fun v => (accum v,.inr (.inr none))) (.goto (fun _ => .inl .start))
  | .inr (.inl l) => liftOuter (Shared.ComplexityBridge.TM2Undelimit.program l)
  | .inr (.inr l) => liftInner (Shared.ComplexityBridge.TM2LiteralClean.program l)

def machine : Turing.FinTM2 where
  K := Key
  k₀ := .inr .stream
  k₁ := .inl (.inl .left)
  Γ := fun _ => Bool
  Λ := Label
  main := .inl .start
  σ := State
  initialState := (false,.inr (.inr none))
  m := program

def outerTerminal (q : Outer.Cfg) : Prop := q.l = some .done ∨ q.l = some .reject
noncomputable instance : DecidablePred outerTerminal := fun _ => Classical.propDecidable _
theorem outer_stable (q : Outer.Cfg) (h : outerTerminal q) : Outer.step q = some q := by
  cases q with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2Undelimit.Label.done ∨ l = some Shared.ComplexityBridge.TM2Undelimit.Label.reject at h
    rcases h with h | h <;> subst l <;> rfl

theorem outer_step (a : Bool) (other : Key → List Bool) (q : Outer.Cfg) (h : ¬ outerTerminal q) :
    machine.step (outerEmbed a other q) = (Outer.step q).map (outerEmbed a other) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | done => exact False.elim (h (Or.inl rfl))
      | reject => exact False.elim (h (Or.inr rfl))
      | header | data | restore =>
        change some (stepAux (liftOuter (Shared.ComplexityBridge.TM2Undelimit.program _)) (a,.inl v) (ostacks S other)) = _
        rw [liftOuter_aux]; rfl

def innerTerminal (q : Inner.Cfg) : Prop := ∃ r : Shared.ComplexityBridge.TM2LiteralEval.Result, q.l = some (.inr (.inr r))
noncomputable instance : DecidablePred innerTerminal := fun _ => Classical.propDecidable _
theorem inner_stable (q : Inner.Cfg) (h : innerTerminal q) : Inner.step q = some q := by
  rcases h with ⟨r,hr⟩
  cases q with
  | mk l v S =>
    change l = some (.inr (.inr r)) at hr
    subst l; rfl

theorem inner_step (a : Bool) (other : Key → List Bool) (q : Inner.Cfg) (h : ¬ innerTerminal q) :
    machine.step (innerEmbed a other q) = (Inner.step q).map (innerEmbed a other) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | inl l =>
        change some (stepAux (liftInner (Shared.ComplexityBridge.TM2LiteralClean.program (.inl l))) (a,.inr (.inl v)) (istacks S other)) = _
        rw [liftInner_aux]; rfl
      | inr l => cases l with
        | inl i =>
          change some (stepAux (liftInner (Shared.ComplexityBridge.TM2LiteralClean.program (.inr (.inl i)))) (a,.inr (.inl v)) (istacks S other)) = _
          rw [liftInner_aux]; rfl
        | inr r => exact False.elim (h ⟨r,rfl⟩)

def stackVals (stream frame witness : List Bool) : Key → List Bool :=
  istacks (Shared.ComplexityBridge.TM2LiteralPreserve.combinedStacks (fun _ => [])
    (Shared.ComplexityBridge.TM2LiteralPreserve.extras frame witness []))
    (fun k => match k with | .inr .stream => stream | _ => [])

def cfg (l : Phase) (a : Bool) (flag : Option Bool) (stream frame witness : List Bool) : machine.Cfg :=
  ⟨some (.inl l),(a,.inr (.inr flag)),stackVals stream frame witness⟩

theorem start_nil (a : Bool) (flag : Option Bool) (frame witness : List Bool) :
    machine.step (cfg .start a flag [] frame witness) = some (cfg (if a then .yes else .no) a none [] frame witness) := by
  cases a <;> rfl

theorem start_cons (a : Bool) (flag : Option Bool) (b : Bool) (tail frame witness : List Bool) :
    machine.step (cfg .start a flag (b::tail) frame witness) =
      some (outerEmbed a (stackVals [] frame witness) (Turing.initList Outer (b::tail))) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [outerEmbed,ostacks,stackVals,istacks,Shared.ComplexityBridge.TM2LiteralPreserve.combinedStacks,
        Shared.ComplexityBridge.TM2LiteralPreserve.extras,Turing.initList,Outer,Shared.ComplexityBridge.TM2Undelimit.machine] <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k <;> simp [outerEmbed,ostacks,stackVals,istacks,Turing.initList,Outer,Shared.ComplexityBridge.TM2Undelimit.machine] <;> rfl

theorem start_delimit (a : Bool) (flag : Option Bool) (payload tail frame witness : List Bool) :
    machine.step (cfg .start a flag (BitstringEncoding.delimit payload ++ tail) frame witness) =
      some (outerEmbed a (stackVals [] frame witness) (Turing.initList Outer (BitstringEncoding.delimit payload ++ tail))) := by
  cases payload with
  | nil => exact start_cons a flag false tail frame witness
  | cons b payload => exact start_cons a flag true (b::BitstringEncoding.delimit payload ++ tail) frame witness

theorem outer_done (a : Bool) (tail payload frame witness : List Bool) :
    machine.step (outerEmbed a (stackVals [] frame witness) (Shared.ComplexityBridge.TM2Undelimit.cfg .done none tail [] payload)) =
      some (innerEmbed a (stackVals tail frame witness)
        (Shared.ComplexityBridge.TM2LiteralClean.embed (Shared.ComplexityBridge.TM2LiteralPreserve.cfg .scanVars none frame witness [] [] [] payload))) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [outerEmbed,innerEmbed,ostacks,istacks,stackVals,
        Shared.ComplexityBridge.TM2Undelimit.cfg,Shared.ComplexityBridge.TM2Undelimit.stackVals,
        Shared.ComplexityBridge.TM2LiteralClean.embed,Shared.ComplexityBridge.TM2LiteralPreserve.cfg,
        Shared.ComplexityBridge.TM2LiteralPreserve.combinedStacks,Shared.ComplexityBridge.TM2LiteralPreserve.sourceStacks,
        Shared.ComplexityBridge.TM2WitnessLookup.stackVals] <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k <;> rfl

theorem outer_rejected (a : Bool) (other : Key → List Bool) (q : Outer.Cfg) (h : q.l = some .reject) :
    ∃ r, machine.step (outerEmbed a other q) = some r ∧ r.l = some (.inl .invalid) := by
  cases q with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2Undelimit.Label.reject at h
    subst l
    exact ⟨⟨some (.inl .invalid),(a,.inl v),ostacks S other⟩,rfl,rfl⟩

theorem inner_done (a b : Bool) (tail frame witness : List Bool) :
    machine.step (innerEmbed a (stackVals tail frame witness)
      (Shared.ComplexityBridge.TM2LiteralClean.finalCfg (if b then .yes else .no) (Shared.ComplexityBridge.TM2LiteralPreserve.extras frame witness []))) =
    some (cfg .start (a || b) none tail frame witness) := by
  cases b <;> cases a <;> rfl

theorem inner_invalid (a : Bool) (tail frame witness : List Bool) :
    ∃ q, machine.step (innerEmbed a (stackVals tail frame witness)
      (Shared.ComplexityBridge.TM2LiteralClean.finalCfg .invalid (Shared.ComplexityBridge.TM2LiteralPreserve.extras frame witness []))) =
      some q ∧ q.l = some (.inl .invalid) := by
  let q := Shared.ComplexityBridge.TM2LiteralClean.finalCfg .invalid (Shared.ComplexityBridge.TM2LiteralPreserve.extras frame witness [])
  exact ⟨⟨some (.inl .invalid),(a,.inr (.inl q.var)),istacks q.stk (stackVals tail frame witness)⟩,rfl,rfl⟩

noncomputable def iterationPolynomial : Polynomial Nat :=
  Polynomial.C 3*Polynomial.X+Polynomial.C 5+Shared.ComplexityBridge.TM2LiteralClean.timePolynomial

theorem iterationPolynomial_eval (n : Nat) :
    iterationPolynomial.eval n = 3*n+5+Shared.ComplexityBridge.TM2LiteralClean.timePolynomial.eval n := by
  simp [iterationPolynomial]

theorem process_one (vars : List (List Bool)) (witness payload tail : List Bool) (a b : Bool) (flag : Option Bool)
    (h : Shared.ComplexityBridge.TM2LiteralEval.evaluate vars witness payload = some b) :
    let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
    let size := frame.length+witness.length+(BitstringEncoding.delimit payload ++ tail).length
    ∃ t ≤ iterationPolynomial.eval size,
      runSteps machine.step t (cfg .start a flag (BitstringEncoding.delimit payload ++ tail) frame witness) =
        some (cfg .start (a || b) none tail frame witness) := by
  let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
  let bits := BitstringEncoding.delimit payload ++ tail
  let size := frame.length+witness.length+bits.length
  let other := stackVals [] frame witness
  let outerEnd := Shared.ComplexityBridge.TM2Undelimit.cfg .done none tail [] payload
  let innerOther := stackVals tail frame witness
  let innerStart := Shared.ComplexityBridge.TM2LiteralClean.embed (Shared.ComplexityBridge.TM2LiteralPreserve.cfg .scanVars none frame witness [] [] [] payload)
  let innerEnd := Shared.ComplexityBridge.TM2LiteralClean.finalCfg (if b then .yes else .no) (Shared.ComplexityBridge.TM2LiteralPreserve.extras frame witness [])
  have hp := Shared.ComplexityBridge.TM2Undelimit.valid_run payload tail
  change runSteps Outer.step (3*payload.length+2) (Turing.initList Outer bits) = some outerEnd at hp
  obtain ⟨x,hx,hxr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Outer.step machine.step (outerEmbed a other) outerTerminal outer_stable (outer_step a other)
    _ (Turing.initList Outer bits) outerEnd (Or.inl rfl) hp
  obtain ⟨n,hn,hr⟩ := Shared.ComplexityBridge.TM2LiteralClean.loaded_progress vars witness payload
  change n ≤ Shared.ComplexityBridge.TM2LiteralClean.timePolynomial.eval (frame.length+witness.length+payload.length) at hn
  have hr' : runSteps Inner.step n innerStart = some innerEnd := by
    cases b <;> simpa [h,innerStart,innerEnd,frame] using hr
  obtain ⟨y,hy,hyr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Inner.step machine.step (innerEmbed a innerOther) innerTerminal inner_stable (inner_step a innerOther)
    n innerStart innerEnd ⟨if b then .yes else .no,rfl⟩ hr'
  have hsize : frame.length+witness.length+payload.length ≤ size := by
    dsimp [size,bits]; simp only [List.length_append,BitstringEncoding.length_delimit]; omega
  have hm := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono Shared.ComplexityBridge.TM2LiteralClean.timePolynomial hsize
  refine ⟨1+x+1+y+1,?_,?_⟩
  · rw [iterationPolynomial_eval]
    change 1+x+1+y+1 ≤ 3*size+5+Shared.ComplexityBridge.TM2LiteralClean.timePolynomial.eval size
    omega
  · change runSteps machine.step (1+x+1+y+1) (cfg .start a flag bits frame witness) = _
    rw [show 1+x+1+y+1 = 1+(x+(1+(y+1))) by omega,runSteps_add]
    change (machine.step (cfg .start a flag bits frame witness)).bind _ = _
    rw [start_delimit]
    change runSteps machine.step (x+(1+(y+1))) (outerEmbed a other (Turing.initList Outer bits)) = _
    rw [runSteps_add,hxr]
    change runSteps machine.step (1+(y+1)) (outerEmbed a other outerEnd) = _
    rw [runSteps_add]
    change (machine.step (outerEmbed a other outerEnd)).bind _ = _
    rw [outer_done]
    change runSteps machine.step (y+1) (innerEmbed a innerOther innerStart) = _
    rw [runSteps_add,hyr]
    exact inner_done a b tail frame witness

theorem bad_outer (input frame witness : List Bool) (a : Bool) (flag : Option Bool) (hne : input ≠ [])
    (hbad : BitstringEncoding.undelimit input = none) :
    ∃ t ≤ input.length+3, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start a flag input frame witness) = some q ∧ q.l = some (.inl .invalid) := by
  obtain ⟨n,hn,scratch,hr⟩ := Shared.ComplexityBridge.TM2Undelimit.invalid_run input [] [] none hbad
  rw [← Shared.ComplexityBridge.TM2Undelimit.initial_eq] at hr
  let finish := Shared.ComplexityBridge.TM2Undelimit.cfg .reject none [] scratch []
  let other := stackVals [] frame witness
  change runSteps Outer.step n (Turing.initList Outer input) = some finish at hr
  obtain ⟨x,hx,hxr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Outer.step machine.step (outerEmbed a other) outerTerminal outer_stable (outer_step a other)
    n (Turing.initList Outer input) finish (Or.inr rfl) hr
  obtain ⟨r,hs,hl⟩ := outer_rejected a other finish rfl
  refine ⟨1+x+1,by omega,r,?_,hl⟩
  cases input with
  | nil => exact False.elim (hne rfl)
  | cons b tail =>
    rw [show 1+x+1 = 1+(x+1) by omega,runSteps_add]
    change (machine.step (cfg .start a flag (b::tail) frame witness)).bind _ = _
    rw [start_cons]
    change runSteps machine.step (x+1) (outerEmbed a other (Turing.initList Outer (b::tail))) = _
    rw [runSteps_add,hxr]
    exact hs

theorem bad_literal (vars : List (List Bool)) (witness payload tail : List Bool) (a : Bool) (flag : Option Bool)
    (h : Shared.ComplexityBridge.TM2LiteralEval.evaluate vars witness payload = none) :
    let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
    let size := frame.length+witness.length+(BitstringEncoding.delimit payload ++ tail).length
    ∃ t ≤ iterationPolynomial.eval size, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start a flag (BitstringEncoding.delimit payload ++ tail) frame witness) = some q ∧
        q.l = some (.inl .invalid) := by
  let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
  let bits := BitstringEncoding.delimit payload ++ tail
  let size := frame.length+witness.length+bits.length
  let other := stackVals [] frame witness
  let outerEnd := Shared.ComplexityBridge.TM2Undelimit.cfg .done none tail [] payload
  let innerOther := stackVals tail frame witness
  let innerStart := Shared.ComplexityBridge.TM2LiteralClean.embed (Shared.ComplexityBridge.TM2LiteralPreserve.cfg .scanVars none frame witness [] [] [] payload)
  let innerEnd := Shared.ComplexityBridge.TM2LiteralClean.finalCfg .invalid (Shared.ComplexityBridge.TM2LiteralPreserve.extras frame witness [])
  have hp := Shared.ComplexityBridge.TM2Undelimit.valid_run payload tail
  change runSteps Outer.step (3*payload.length+2) (Turing.initList Outer bits) = some outerEnd at hp
  obtain ⟨x,hx,hxr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Outer.step machine.step (outerEmbed a other) outerTerminal outer_stable (outer_step a other)
    _ (Turing.initList Outer bits) outerEnd (Or.inl rfl) hp
  obtain ⟨n,hn,hr⟩ := Shared.ComplexityBridge.TM2LiteralClean.loaded_progress vars witness payload
  change n ≤ Shared.ComplexityBridge.TM2LiteralClean.timePolynomial.eval (frame.length+witness.length+payload.length) at hn
  have hr' : runSteps Inner.step n innerStart = some innerEnd := by simpa [h,innerStart,innerEnd,frame] using hr
  obtain ⟨y,hy,hyr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    Inner.step machine.step (innerEmbed a innerOther) innerTerminal inner_stable (inner_step a innerOther)
    n innerStart innerEnd ⟨.invalid,rfl⟩ hr'
  obtain ⟨q,hq,hl⟩ := inner_invalid a tail frame witness
  have hsize : frame.length+witness.length+payload.length ≤ size := by
    dsimp [size,bits]; simp only [List.length_append,BitstringEncoding.length_delimit]; omega
  have hm := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono Shared.ComplexityBridge.TM2LiteralClean.timePolynomial hsize
  refine ⟨1+x+1+y+1,?_,q,?_,hl⟩
  · rw [iterationPolynomial_eval]
    change 1+x+1+y+1 ≤ 3*size+5+Shared.ComplexityBridge.TM2LiteralClean.timePolynomial.eval size
    omega
  · change runSteps machine.step (1+x+1+y+1) (cfg .start a flag bits frame witness) = _
    rw [show 1+x+1+y+1 = 1+(x+(1+(y+1))) by omega,runSteps_add]
    change (machine.step (cfg .start a flag bits frame witness)).bind _ = _
    rw [start_delimit]
    change runSteps machine.step (x+(1+(y+1))) (outerEmbed a other (Turing.initList Outer bits)) = _
    rw [runSteps_add,hxr]
    change runSteps machine.step (1+(y+1)) (outerEmbed a other outerEnd) = _
    rw [runSteps_add]
    change (machine.step (outerEmbed a other outerEnd)).bind _ = _
    rw [outer_done]
    change runSteps machine.step (y+1) (innerEmbed a innerOther innerStart) = _
    rw [runSteps_add,hyr]
    exact hq

/-- Evaluate every original literal block, accumulating disjunction. Invalid
framing and invalid literals return none, even after a true literal. -/
def evaluate (vars : List (List Bool)) (witness input : List Bool) (a : Bool) : Option Bool :=
  if input = [] then some a else
    match h : BitstringEncoding.undelimit input with
    | none => none
    | some (payload,tail) =>
      match Shared.ComplexityBridge.TM2LiteralEval.evaluate vars witness payload with
      | none => none
      | some b => evaluate vars witness tail (a || b)
termination_by input.length
decreasing_by
  have he := Shared.ComplexityBridge.CNFWitness.undelimit_sound input payload tail h
  have hl := congrArg List.length he
  simp only [List.length_append,BitstringEncoding.length_delimit] at hl
  omega

theorem evaluate_nil (vars : List (List Bool)) (witness : List Bool) (a : Bool) : evaluate vars witness [] a = some a := by rw [evaluate]; rfl

theorem evaluate_bad_frame (vars : List (List Bool)) (witness : List Bool) (a x : Bool) (xs : List Bool)
    (h : BitstringEncoding.undelimit (x::xs) = none) : evaluate vars witness (x::xs) a = none := by
  rw [evaluate]
  simp only [List.cons_ne_nil,if_false]
  split <;> simp_all

theorem evaluate_frame (vars : List (List Bool)) (witness payload tail : List Bool) (a : Bool) :
    evaluate vars witness (BitstringEncoding.delimit payload ++ tail) a =
      (Shared.ComplexityBridge.TM2LiteralEval.evaluate vars witness payload).bind (fun b => evaluate vars witness tail (a || b)) := by
  have hne : BitstringEncoding.delimit payload ++ tail ≠ [] := by
    intro he
    have hl := congrArg List.length he
    simp only [List.length_append,BitstringEncoding.length_delimit,List.length_nil] at hl
    omega
  rw [evaluate,if_neg hne,BitstringEncoding.undelimit_delimit]
  cases he : Shared.ComplexityBridge.TM2LiteralEval.evaluate vars witness payload <;> simp [he]

/-- Every literal comparison and the entire clause loop finish within a
polynomial in the loaded occurrence, witness, and clause lengths. -/
theorem evaluation_run (vars : List (List Bool)) (witness input : List Bool) (a : Bool) (flag : Option Bool) :
    let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
    let size := frame.length+witness.length+input.length
    ∃ t ≤ input.length*iterationPolynomial.eval size+1, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start a flag input frame witness) = some q ∧
      q.l = some (.inl (match evaluate vars witness input a with
        | none => .invalid | some true => .yes | some false => .no)) := by
  let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
  cases input with
  | nil =>
    refine ⟨1,by simp,cfg (if a then .yes else .no) a none [] frame witness,start_nil a flag frame witness,?_⟩
    cases a <;> simp [evaluate_nil,cfg]
  | cons x xs =>
    let input := x::xs
    let size := frame.length+witness.length+input.length
    change ∃ t ≤ input.length*iterationPolynomial.eval size+1, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start a flag input frame witness) = some q ∧
      q.l = some (.inl (match evaluate vars witness input a with | none => .invalid | some true => .yes | some false => .no))
    have hpos : 1 ≤ input.length := by simp [input]
    have hK : 4 ≤ iterationPolynomial.eval size := by rw [iterationPolynomial_eval]; omega
    have hmul := Nat.mul_le_mul_left input.length hK
    have hinput : input.length ≤ size := by dsimp [size]; omega
    cases ho : BitstringEncoding.undelimit input with
    | none =>
      obtain ⟨t,ht,q,hr,hq⟩ := bad_outer input frame witness a flag (by simp [input]) ho
      refine ⟨t,by omega,q,hr,?_⟩
      have hv : evaluate vars witness input a = none := evaluate_bad_frame vars witness a x xs ho
      simpa [hv] using hq
    | some pair =>
      rcases pair with ⟨payload,tail⟩
      have he := Shared.ComplexityBridge.CNFWitness.undelimit_sound input payload tail ho
      have hlt : tail.length < input.length := by
        have hl := congrArg List.length he
        simp only [List.length_append,BitstringEncoding.length_delimit] at hl
        omega
      cases hb : Shared.ComplexityBridge.TM2LiteralEval.evaluate vars witness payload with
      | none =>
        obtain ⟨t,ht,q,hr,hq⟩ := bad_literal vars witness payload tail a flag hb
        change t ≤ iterationPolynomial.eval (frame.length+witness.length+(BitstringEncoding.delimit payload ++ tail).length) at ht
        rw [he] at ht
        change t ≤ iterationPolynomial.eval size at ht
        have hbound : iterationPolynomial.eval size ≤ input.length*iterationPolynomial.eval size := by
          have hh := Nat.mul_le_mul_right (iterationPolynomial.eval size) hpos
          simpa using hh
        refine ⟨t,by omega,q,?_,?_⟩
        · simpa [he] using hr
        · have hv : evaluate vars witness input a = none := by rw [← he,evaluate_frame,hb]; rfl
          simpa [hv] using hq
      | some b =>
        obtain ⟨t,ht,hr⟩ := process_one vars witness payload tail a b flag hb
        change t ≤ iterationPolynomial.eval (frame.length+witness.length+(BitstringEncoding.delimit payload ++ tail).length) at ht
        rw [he] at ht
        change t ≤ iterationPolynomial.eval size at ht
        obtain ⟨u,hu,q,hur,hq⟩ := evaluation_run vars witness tail (a || b) none
        let sizeTail := frame.length+witness.length+tail.length
        change u ≤ tail.length*iterationPolynomial.eval sizeTail+1 at hu
        have hsize : sizeTail ≤ size := by dsimp [sizeTail,size]; omega
        have hm := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono iterationPolynomial hsize
        have hmb := Nat.mul_le_mul_left tail.length hm
        have htail := Nat.mul_le_mul_right (iterationPolynomial.eval size) (show tail.length+1 ≤ input.length by omega)
        have hbound : t+u ≤ input.length*iterationPolynomial.eval size+1 := by
          rw [Nat.add_mul,Nat.one_mul] at htail
          omega
        refine ⟨t+u,hbound,q,?_,?_⟩
        · rw [← he,runSteps_add,hr]; exact hur
        · have hv : evaluate vars witness input a = evaluate vars witness tail (a || b) := by rw [← he,evaluate_frame,hb]; rfl
          simpa [hv] using hq
termination_by input.length

theorem evaluate_framed (vars : List (List Bool)) (witness : List Bool) (literals : List (List Bool)) (a : Bool) :
    evaluate vars witness (Shared.ComplexityBridge.TM2WitnessLookup.frames literals) a =
      (literals.mapM (Shared.ComplexityBridge.TM2LiteralEval.evaluate vars witness)).map (fun bs => a || bs.any id) := by
  induction literals generalizing a with
  | nil => simp [Shared.ComplexityBridge.TM2WitnessLookup.frames,evaluate_nil]
  | cons p ps ih =>
    rw [Shared.ComplexityBridge.TM2WitnessLookup.frames_cons,evaluate_frame]
    cases hp : Shared.ComplexityBridge.TM2LiteralEval.evaluate vars witness p with
    | none => simp [hp,List.mapM_cons]
    | some b =>
      simp only [hp,Option.bind_some]
      rw [ih]
      cases ht : ps.mapM (Shared.ComplexityBridge.TM2LiteralEval.evaluate vars witness) with
      | none => simp [List.mapM_cons,hp,ht]
      | some bs => cases a <;> cases b <;> simp [List.mapM_cons,hp,ht]

theorem evaluate_bad_blocks (vars : List (List Bool)) (witness input : List Bool) (a : Bool)
    (hbad : BitstringEncoding.undelimitBlocks input = none) : evaluate vars witness input a = none := by
  cases input with
  | nil => simp [BitstringEncoding.undelimitBlocks,BitstringEncoding.undelimitBlocksAux] at hbad
  | cons x xs =>
    cases ho : BitstringEncoding.undelimit (x::xs) with
    | none => exact evaluate_bad_frame vars witness a x xs ho
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
            rw [hblocks]; exact he
          have hv := BitstringEncoding.undelimitBlocks_flatten_delimit (payload::blocks)
          change BitstringEncoding.undelimitBlocks (Shared.ComplexityBridge.TM2WitnessLookup.frames (payload::blocks)) = _ at hv
          rw [hfull,hbad] at hv
          contradiction
      have hlt : tail.length < (x::xs).length := by
        have hl := congrArg List.length he
        simp only [List.length_append,BitstringEncoding.length_delimit,List.length_cons] at hl
        simp only [List.length_cons]; omega
      rw [← he,evaluate_frame]
      cases hn : Shared.ComplexityBridge.TM2LiteralEval.evaluate vars witness payload with
      | none => rfl
      | some b => simpa [hn] using evaluate_bad_blocks vars witness tail (a || b) htail
termination_by input.length

/-- The finite clause loop computes the previously proved raw clause
semantics on every bitstring, including malformed data. -/
theorem evaluate_correct (vars : List (List Bool)) (witness input : List Bool) :
    evaluate vars witness input false = Shared.ComplexityBridge.RawCNFEval.clause vars witness input := by
  unfold Shared.ComplexityBridge.RawCNFEval.clause
  cases h : BitstringEncoding.undelimitBlocks input with
  | none => simpa [h] using evaluate_bad_blocks vars witness input false h
  | some literals =>
    have he := Shared.ComplexityBridge.CNFWitness.blocks_sound input literals h
    change Shared.ComplexityBridge.TM2WitnessLookup.frames literals = input at he
    rw [← he,evaluate_framed]
    simp


noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.X*iterationPolynomial+Polynomial.C 1

theorem timePolynomial_eval (n : Nat) : timePolynomial.eval n = n*iterationPolynomial.eval n+1 := by
  simp [timePolynomial]

/-- A successful clause run restores the occurrence and witness stacks and
empties all call working stacks, making it reusable by an outer formula loop. -/
theorem evaluation_success_run (vars : List (List Bool)) (witness input : List Bool) (a : Bool) (flag : Option Bool) (b : Bool)
    (h : evaluate vars witness input a = some b) :
    let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
    let size := frame.length+witness.length+input.length
    ∃ t ≤ input.length*iterationPolynomial.eval size+1,
      runSteps machine.step t (cfg .start a flag input frame witness) =
        some (cfg (if b then .yes else .no) b none [] frame witness) := by
  let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
  cases input with
  | nil =>
    rw [evaluate_nil] at h
    have hb : a = b := Option.some.inj h
    subst b
    exact ⟨1,by simp,start_nil a flag frame witness⟩
  | cons x xs =>
    let input := x::xs
    let size := frame.length+witness.length+input.length
    change evaluate vars witness input a = some b at h
    change ∃ t ≤ input.length*iterationPolynomial.eval size+1,
      runSteps machine.step t (cfg .start a flag input frame witness) =
        some (cfg (if b then .yes else .no) b none [] frame witness)
    cases ho : BitstringEncoding.undelimit input with
    | none =>
      have hv : evaluate vars witness input a = none := evaluate_bad_frame vars witness a x xs ho
      rw [hv] at h; contradiction
    | some pair =>
      rcases pair with ⟨payload,tail⟩
      have he := Shared.ComplexityBridge.CNFWitness.undelimit_sound input payload tail ho
      have hlt : tail.length < input.length := by
        have hl := congrArg List.length he
        simp only [List.length_append,BitstringEncoding.length_delimit] at hl
        omega
      cases hv : Shared.ComplexityBridge.TM2LiteralEval.evaluate vars witness payload with
      | none =>
        rw [← he,evaluate_frame,hv] at h
        contradiction
      | some v =>
        have ht : evaluate vars witness tail (a || v) = some b := by
          rw [← he,evaluate_frame,hv] at h
          exact h
        obtain ⟨t,htbound,hr⟩ := process_one vars witness payload tail a v flag hv
        change t ≤ iterationPolynomial.eval (frame.length+witness.length+(BitstringEncoding.delimit payload ++ tail).length) at htbound
        rw [he] at htbound
        change t ≤ iterationPolynomial.eval size at htbound
        obtain ⟨u,hubound,hur⟩ := evaluation_success_run vars witness tail (a || v) none b ht
        let sizeTail := frame.length+witness.length+tail.length
        change u ≤ tail.length*iterationPolynomial.eval sizeTail+1 at hubound
        have hsize : sizeTail ≤ size := by dsimp [sizeTail,size]; omega
        have hm := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono iterationPolynomial hsize
        have hmb := Nat.mul_le_mul_left tail.length hm
        have htail := Nat.mul_le_mul_right (iterationPolynomial.eval size) (show tail.length+1 ≤ input.length by omega)
        have hbound : t+u ≤ input.length*iterationPolynomial.eval size+1 := by
          rw [Nat.add_mul,Nat.one_mul] at htail
          omega
        refine ⟨t+u,hbound,?_⟩
        rw [← he,runSteps_add,hr]
        exact hur
termination_by input.length

/-- Clause acceptance agrees with the public CNF evaluator and has a single
polynomial bound in the total loaded input length. -/
theorem clause_success_run (vars : List (List Bool)) (witness input : List Bool) (clause : Shared.ComplexityBridge.CNF.Clause)
    (h : (BitstringEncoding.bitDecode input : Option Shared.ComplexityBridge.CNF.Clause) = some clause) :
    let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
    let size := frame.length+witness.length+input.length
    let b := Shared.ComplexityBridge.CNF.evalClause
      (Shared.ComplexityBridge.CNF.assignment (vars.map Computability.decodeNat) witness) clause
    ∃ t ≤ timePolynomial.eval size,
      runSteps machine.step t (cfg .start false none input frame witness) =
        some (cfg (if b then .yes else .no) b none [] frame witness) := by
  let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
  let size := frame.length+witness.length+input.length
  let b := Shared.ComplexityBridge.CNF.evalClause
    (Shared.ComplexityBridge.CNF.assignment (vars.map Computability.decodeNat) witness) clause
  have he : evaluate vars witness input false = some b := by
    rw [evaluate_correct,Shared.ComplexityBridge.RawCNFEval.clause_eq,h]
    rfl
  obtain ⟨t,ht,hr⟩ := evaluation_success_run vars witness input false none b he
  change t ≤ input.length*iterationPolynomial.eval size+1 at ht
  have hsize : input.length ≤ size := by dsimp [size]; omega
  have hm := Nat.mul_le_mul_right (iterationPolynomial.eval size) hsize
  refine ⟨t,?_,hr⟩
  rw [timePolynomial_eval]
  change t ≤ size*iterationPolynomial.eval size+1
  omega


/-- Total all-bitstrings clause result, including malformed frames and
literals, with one polynomial bound in the loaded input size. -/
theorem clause_progress (vars : List (List Bool)) (witness input : List Bool) :
    let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
    let size := frame.length+witness.length+input.length
    ∃ t ≤ timePolynomial.eval size, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start false none input frame witness) = some q ∧
      q.l = some (.inl (match Shared.ComplexityBridge.RawCNFEval.clause vars witness input with
        | none => .invalid | some true => .yes | some false => .no)) := by
  let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
  let size := frame.length+witness.length+input.length
  obtain ⟨t,ht,q,hr,hlabel⟩ := evaluation_run vars witness input false none
  change t ≤ input.length*iterationPolynomial.eval size+1 at ht
  have hsize : input.length ≤ size := by dsimp [size]; omega
  have hm := Nat.mul_le_mul_right (iterationPolynomial.eval size) hsize
  refine ⟨t,?_,q,hr,?_⟩
  · rw [timePolynomial_eval]
    change t ≤ size*iterationPolynomial.eval size+1
    omega
  · simpa [evaluate_correct] using hlabel

/-- Malformed clauses always produce the invalid continuation. -/
theorem clause_invalid (vars : List (List Bool)) (witness input : List Bool)
    (h : (BitstringEncoding.bitDecode input : Option Shared.ComplexityBridge.CNF.Clause) = none) :
    let frame := Shared.ComplexityBridge.TM2WitnessLookup.frames vars
    let size := frame.length+witness.length+input.length
    ∃ t ≤ timePolynomial.eval size, ∃ q : machine.Cfg,
      runSteps machine.step t (cfg .start false none input frame witness) = some q ∧ q.l = some (.inl .invalid) := by
  have he : Shared.ComplexityBridge.RawCNFEval.clause vars witness input = none := by
    rw [Shared.ComplexityBridge.RawCNFEval.clause_eq,h]; rfl
  simpa [he] using clause_progress vars witness input


namespace Fixtures
example : machine.step (cfg .start false none [] [] []) = some (cfg .no false none [] [] []) := by rfl
set_option maxRecDepth 4096 in
example : (runSteps machine.step 33 (cfg .start false none
    (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false,false]]) [] [])).map
    (fun q => match q.l with | some (.inl .yes) => true | _ => false) = some true := by
  change (Option.map (fun q => match q.l with | some (.inl .yes) => true | _ => false)
    (runSteps machine.step 33 (cfg .start false none
      (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false,false]]) [] [])) : Option Bool) = _
  decide
set_option maxRecDepth 4096 in
example : (runSteps machine.step 33 (cfg .start false none
    (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false,true]]) [] [])).map
    (fun q => match q.l with | some (.inl .no) => true | _ => false) = some true := by
  change (Option.map (fun q => match q.l with | some (.inl .no) => true | _ => false)
    (runSteps machine.step 33 (cfg .start false none
      (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false,true]]) [] [])) : Option Bool) = _
  decide
-- Even after the first true literal, the second malformed literal is rejected.
set_option maxRecDepth 4096 in
example : (runSteps machine.step 58 (cfg .start false none
    (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false,false],[false]]) [] [])).map
    (fun q => match q.l with | some (.inl .invalid) => true | _ => false) = some true := by
  change (Option.map (fun q => match q.l with | some (.inl .invalid) => true | _ => false)
    (runSteps machine.step 58 (cfg .start false none
      (Shared.ComplexityBridge.TM2WitnessLookup.frames [[false,false],[false]]) [] [])) : Option Bool) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2ClauseEval
