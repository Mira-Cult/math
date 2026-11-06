import Mathlib.Logic.Equiv.Bool
import Shared.ComplexityBridge.TM2GateTransfer
import Shared.ComplexityBridge.TM2PairTotalPoly

set_option linter.unusedSimpArgs false
namespace Shared.ComplexityBridge.TM2CutoffCompose
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Terms := Shared.Codes.NumericPolynomial.Terms
abbrev GateKey := Shared.ComplexityBridge.TM2CutoffGate.Key
abbrev Key (tm : Turing.FinTM2) := Shared.ComplexityBridge.TM2GateTransfer.Key tm
abbrev Alphabet (tm : Turing.FinTM2) := Shared.ComplexityBridge.TM2GateTransfer.Alphabet tm
abbrev Label (ts : Terms) (tm : Turing.FinTM2) := Shared.ComplexityBridge.TM2GateClean.Label ts ⊕
  (Shared.ComplexityBridge.TM2GateTransfer.Label ⊕ tm.Λ)
abbrev State (tm : Turing.FinTM2) := Shared.ComplexityBridge.TM2GateClean.State ⊕ (Option Bool ⊕ tm.σ)

def gateState (tm : Turing.FinTM2) : State tm → Shared.ComplexityBridge.TM2GateClean.State
  | .inl v => v | .inr _ => .inl (.inl none)
def transferState (tm : Turing.FinTM2) : State tm → Option Bool
  | .inr (.inl v) => v | _ => none
def checkerState (tm : Turing.FinTM2) : State tm → tm.σ
  | .inr (.inr v) => v | _ => tm.initialState

def stackFamily (tm : Turing.FinTM2) (G : GateKey → List Bool) (S : (k : tm.K) → List (tm.Γ k)) :
    (k : Key tm) → List (Alphabet tm k)
  | .inl k => G k
  | .inr k => S k

set_option backward.isDefEq.respectTransparency false in
theorem update_gate (tm : Turing.FinTM2) (G : GateKey → List Bool) (S : (k : tm.K) → List (tm.Γ k))
    (j : GateKey) (xs : List Bool) :
    Function.update (stackFamily tm G S) (.inl j) xs = stackFamily tm (Function.update G j xs) S := by
  funext k
  cases k with
  | inl q =>
    by_cases h : q = j
    · subst q; simp [stackFamily]
    · have hh : (Sum.inl q : Key tm) ≠ .inl j := by simpa using h
      simp [stackFamily,Function.update_of_ne h,Function.update_of_ne hh]
  | inr q => simp [stackFamily,Function.update]

set_option backward.isDefEq.respectTransparency false in
theorem update_checker (tm : Turing.FinTM2) (G : GateKey → List Bool) (S : (k : tm.K) → List (tm.Γ k))
    (j : tm.K) (xs : List (tm.Γ j)) :
    Function.update (stackFamily tm G S) (.inr j) xs = stackFamily tm G (Function.update S j xs) := by
  funext k
  cases k with
  | inl q => simp [stackFamily,Function.update]
  | inr q =>
    by_cases h : q = j
    · subst q; simp [stackFamily]
    · have hh : (Sum.inr q : Key tm) ≠ .inr j := by simpa using h
      simp [stackFamily,Function.update_of_ne h,Function.update_of_ne hh]

def gateEmbed (ts : Terms) (tm : Turing.FinTM2) (S : (k : tm.K) → List (tm.Γ k))
    (q : (Shared.ComplexityBridge.TM2GateClean.machine ts).Cfg) : Cfg (Alphabet tm) (Label ts tm) (State tm) :=
  ⟨q.l.map Sum.inl,.inl q.var,stackFamily tm q.stk S⟩
def transferEmbed (ts : Terms) (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool)
    (q : (Shared.ComplexityBridge.TM2GateTransfer.machine tm ea).Cfg) : Cfg (Alphabet tm) (Label ts tm) (State tm) :=
  ⟨q.l.map (fun l => .inr (.inl l)),.inr (.inl q.var),q.stk⟩
def checkerEmbed (ts : Terms) (tm : Turing.FinTM2) (G : GateKey → List Bool) (q : tm.Cfg) :
    Cfg (Alphabet tm) (Label ts tm) (State tm) :=
  ⟨q.l.map (fun l => .inr (.inr l)),match q.l with | none => .inl (.inl (.inl none)) | some _ => .inr (.inr q.var),stackFamily tm G q.stk⟩

def liftGate (ts : Terms) (tm : Turing.FinTM2) :
    Stmt (fun _ : GateKey => Bool) (Shared.ComplexityBridge.TM2GateClean.Label ts) Shared.ComplexityBridge.TM2GateClean.State →
    Stmt (Alphabet tm) (Label ts tm) (State tm)
  | .push j f q => .push (.inl j) (fun v => f (gateState tm v)) (liftGate ts tm q)
  | .peek j f q => .peek (.inl j) (fun v h => .inl (f (gateState tm v) h)) (liftGate ts tm q)
  | .pop j f q => .pop (.inl j) (fun v h => .inl (f (gateState tm v) h)) (liftGate ts tm q)
  | .load f q => .load (fun v => .inl (f (gateState tm v))) (liftGate ts tm q)
  | .branch f q r => .branch (fun v => f (gateState tm v)) (liftGate ts tm q) (liftGate ts tm r)
  | .goto f => .goto (fun v => .inl (f (gateState tm v)))
  | .halt => .halt

def liftTransfer (ts : Terms) (tm : Turing.FinTM2) :
    Stmt (Alphabet tm) Shared.ComplexityBridge.TM2GateTransfer.Label (Option Bool) →
    Stmt (Alphabet tm) (Label ts tm) (State tm)
  | .push j f q => .push j (fun v => f (transferState tm v)) (liftTransfer ts tm q)
  | .peek j f q => .peek j (fun v h => .inr (.inl (f (transferState tm v) h))) (liftTransfer ts tm q)
  | .pop j f q => .pop j (fun v h => .inr (.inl (f (transferState tm v) h))) (liftTransfer ts tm q)
  | .load f q => .load (fun v => .inr (.inl (f (transferState tm v)))) (liftTransfer ts tm q)
  | .branch f q r => .branch (fun v => f (transferState tm v)) (liftTransfer ts tm q) (liftTransfer ts tm r)
  | .goto f => .goto (fun v => .inr (.inl (f (transferState tm v))))
  | .halt => .halt

def liftChecker (ts : Terms) (tm : Turing.FinTM2) : tm.Stmt → Stmt (Alphabet tm) (Label ts tm) (State tm)
  | .push j f q => .push (.inr j) (fun v => f (checkerState tm v)) (liftChecker ts tm q)
  | .peek j f q => .peek (.inr j) (fun v h => .inr (.inr (f (checkerState tm v) h))) (liftChecker ts tm q)
  | .pop j f q => .pop (.inr j) (fun v h => .inr (.inr (f (checkerState tm v) h))) (liftChecker ts tm q)
  | .load f q => .load (fun v => .inr (.inr (f (checkerState tm v)))) (liftChecker ts tm q)
  | .branch f q r => .branch (fun v => f (checkerState tm v)) (liftChecker ts tm q) (liftChecker ts tm r)
  | .goto f => .goto (fun v => .inr (.inr (f (checkerState tm v))))
  | .halt => .load (fun _ => .inl (.inl (.inl none))) .halt

set_option backward.isDefEq.respectTransparency false in
theorem liftGate_aux (ts : Terms) (tm : Turing.FinTM2)
    (q : Stmt (fun _ : GateKey => Bool) (Shared.ComplexityBridge.TM2GateClean.Label ts) Shared.ComplexityBridge.TM2GateClean.State)
    (v : Shared.ComplexityBridge.TM2GateClean.State) (G : GateKey → List Bool) (S : (k : tm.K) → List (tm.Γ k)) :
    stepAux (liftGate ts tm q) (.inl v) (stackFamily tm G S) = gateEmbed ts tm S (stepAux q v G) := by
  induction q generalizing v G with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih =>
    simp only [liftGate,stepAux,gateState,stackFamily]
    rw [update_gate]
    exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih =>
    simp only [liftGate,stepAux,gateState,stackFamily]
    rw [update_gate]
    exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftGate,stepAux,gateState,h,ihq,ihr]

set_option backward.isDefEq.respectTransparency false in
theorem liftTransfer_aux (ts : Terms) (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool)
    (q : Stmt (Alphabet tm) Shared.ComplexityBridge.TM2GateTransfer.Label (Option Bool))
    (v : Option Bool) (S : (k : Key tm) → List (Alphabet tm k)) :
    stepAux (liftTransfer ts tm q) (.inr (.inl v)) S = transferEmbed ts tm ea (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih => exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih => exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftTransfer,stepAux,transferState,h,ihq,ihr]

set_option backward.isDefEq.respectTransparency false in
theorem liftChecker_aux (ts : Terms) (tm : Turing.FinTM2) (q : tm.Stmt)
    (v : tm.σ) (S : (k : tm.K) → List (tm.Γ k)) (G : GateKey → List Bool) :
    stepAux (liftChecker ts tm q) (.inr (.inr v)) (stackFamily tm G S) = checkerEmbed ts tm G (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | push j f q ih =>
    simp only [liftChecker,stepAux,checkerState,stackFamily]
    rw [update_checker]
    exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih =>
    simp only [liftChecker,stepAux,checkerState,stackFamily]
    rw [update_checker]
    exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftChecker,stepAux,checkerState,h,ihq,ihr]

/-- Redirect the cleaned gate to a two-pass copy or a discard. The verifier's
false output is produced only after the reject path has cleared all input. -/
def program (ts : Terms) (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool) :
    Label ts tm → Stmt (Alphabet tm) (Label ts tm) (State tm)
  | .inl (.inl l) => liftGate ts tm (Shared.ComplexityBridge.TM2GateClean.program ts (.inl l))
  | .inl (.inr l) => if l = Shared.ComplexityBridge.TM2GateSweep.done then
      .branch (fun v => (Shared.ComplexityBridge.TM2GateClean.sweepState (gateState tm v)).1)
        (.load (fun _ => .inr (.inl none)) (.goto (fun _ => .inr (.inl .load))))
        (.load (fun _ => .inr (.inl none)) (.goto (fun _ => .inr (.inl .discard))))
    else liftGate ts tm (Shared.ComplexityBridge.TM2GateClean.program ts (.inr l))
  | .inr (.inl .ready) => .load (fun _ => .inr (.inr tm.initialState)) (.goto (fun _ => .inr (.inr tm.main)))
  | .inr (.inl .rejected) => .push (.inr tm.k₁) (fun _ => eb.symm false)
      (.load (fun _ => .inl (.inl (.inl none))) .halt)
  | .inr (.inl l) => liftTransfer ts tm (Shared.ComplexityBridge.TM2GateTransfer.program tm ea l)
  | .inr (.inr l) => liftChecker ts tm (tm.m l)

def machine (ts : Terms) (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool) : Turing.FinTM2 := by
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  exact {
    K := Key tm
    k₀ := .inl (.inl false)
    k₁ := .inr tm.k₁
    Γ := Alphabet tm
    Λ := Label ts tm
    main := .inl (.inl (.inl .start))
    σ := State tm
    initialState := .inl (.inl (.inl none))
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := program ts tm ea eb }

def gateTerminal (ts : Terms) (q : (Shared.ComplexityBridge.TM2GateClean.machine ts).Cfg) : Prop :=
  q.l = some (.inr Shared.ComplexityBridge.TM2GateSweep.done)
noncomputable instance (ts : Terms) : DecidablePred (gateTerminal ts) := fun _ => Classical.propDecidable _

set_option backward.isDefEq.respectTransparency false in
theorem gate_stable (ts : Terms) (q : (Shared.ComplexityBridge.TM2GateClean.machine ts).Cfg)
    (h : gateTerminal ts q) : (Shared.ComplexityBridge.TM2GateClean.machine ts).step q = some q := by
  cases q with
  | mk l v S =>
    change l = some (.inr Shared.ComplexityBridge.TM2GateSweep.done) at h
    subst l
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem gate_step (ts : Terms) (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (S : (k : tm.K) → List (tm.Γ k)) (q : (Shared.ComplexityBridge.TM2GateClean.machine ts).Cfg)
    (h : ¬ gateTerminal ts q) :
    (machine ts tm ea eb).step (gateEmbed ts tm S q) =
      ((Shared.ComplexityBridge.TM2GateClean.machine ts).step q).map (gateEmbed ts tm S) := by
  cases q with
  | mk l v G => cases l with
    | none => rfl
    | some l => cases l with
      | inl l =>
        change some (stepAux (liftGate ts tm (Shared.ComplexityBridge.TM2GateClean.program ts (.inl l))) (.inl v) (stackFamily tm G S)) = _
        rw [liftGate_aux]; rfl
      | inr l =>
        have hl : l ≠ Shared.ComplexityBridge.TM2GateSweep.done := by
          intro he
          apply h
          change (some (.inr l) : Option (Shared.ComplexityBridge.TM2GateClean.Label ts)) = some (.inr Shared.ComplexityBridge.TM2GateSweep.done)
          rw [he]
        change some (stepAux (program ts tm ea eb (.inl (.inr l))) (.inl v) (stackFamily tm G S)) = _
        simp only [program,if_neg hl]
        rw [liftGate_aux]; rfl

def transferTerminal (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool)
    (q : (Shared.ComplexityBridge.TM2GateTransfer.machine tm ea).Cfg) : Prop :=
  q.l = some .ready ∨ q.l = some .rejected
noncomputable instance (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) : DecidablePred (transferTerminal tm ea) :=
  fun _ => Classical.propDecidable _

set_option backward.isDefEq.respectTransparency false in
theorem transfer_stable (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool)
    (q : (Shared.ComplexityBridge.TM2GateTransfer.machine tm ea).Cfg) (h : transferTerminal tm ea q) :
    (Shared.ComplexityBridge.TM2GateTransfer.machine tm ea).step q = some q := by
  cases q with
  | mk l v S =>
    change l = some .ready ∨ l = some .rejected at h
    rcases h with h | h <;> subst l <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem transfer_step (ts : Terms) (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (q : (Shared.ComplexityBridge.TM2GateTransfer.machine tm ea).Cfg) (h : ¬ transferTerminal tm ea q) :
    (machine ts tm ea eb).step (transferEmbed ts tm ea q) =
      ((Shared.ComplexityBridge.TM2GateTransfer.machine tm ea).step q).map (transferEmbed ts tm ea) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l => cases l with
      | ready => exact False.elim (h (Or.inl rfl))
      | rejected => exact False.elim (h (Or.inr rfl))
      | load | restore | discard =>
        change some (stepAux (liftTransfer ts tm (Shared.ComplexityBridge.TM2GateTransfer.program tm ea _)) (.inr (.inl v)) S) = _
        rw [liftTransfer_aux]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem checker_step (ts : Terms) (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (G : GateKey → List Bool) (q : tm.Cfg) :
    (machine ts tm ea eb).step (checkerEmbed ts tm G q) = (tm.step q).map (checkerEmbed ts tm G) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftChecker ts tm (tm.m l)) (.inr (.inr v)) (stackFamily tm G S)) = _
      rw [liftChecker_aux]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem checker_run (ts : Terms) (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (G : GateKey → List Bool) (q : tm.Cfg) (n : Nat) :
    runSteps (machine ts tm ea eb).step n (checkerEmbed ts tm G q) = (runSteps tm.step n q).map (checkerEmbed ts tm G) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front,runSteps_front,checker_step]
    cases h : tm.step q with
    | none => rfl
    | some q' => exact ih q'

theorem gateStacks_empty_aux (bits : List Bool) :
    Shared.ComplexityBridge.TM2GateSweep.stackVals bits (fun _ => []) =
      Shared.ComplexityBridge.TM2GateTransfer.gateStacks bits [] := by
  funext k
  cases k with
  | inl b => cases b <;> rfl
  | inr k => cases k with
    | inl u => cases u; rfl
    | inr k => cases k with
      | inl b => cases b <;> rfl
      | inr j => cases j <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem initial_eq (ts : Terms) (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (bits : List Bool) :
    Turing.initList (machine ts tm ea eb) bits = gateEmbed ts tm (Turing.initList tm []).stk
      (Turing.initList (Shared.ComplexityBridge.TM2GateClean.machine ts) bits) := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1
  funext k
  cases k with
  | inl k =>
    cases k with
    | inl b => cases b <;> simp [machine,Shared.ComplexityBridge.TM2GateClean.machine,gateEmbed,stackFamily,Turing.initList,Function.update] <;> rfl
    | inr j => cases j with
      | inl u => cases u; simp [machine,Shared.ComplexityBridge.TM2GateClean.machine,gateEmbed,stackFamily,Turing.initList,Function.update]
      | inr j => cases j with
        | inl b => cases b <;> simp [machine,Shared.ComplexityBridge.TM2GateClean.machine,gateEmbed,stackFamily,Turing.initList,Function.update]
        | inr a => cases a <;> simp [machine,Shared.ComplexityBridge.TM2GateClean.machine,gateEmbed,stackFamily,Turing.initList,Function.update]
  | inr j =>
    by_cases h : j = tm.k₀
    · subst j; simp [machine,gateEmbed,stackFamily,Turing.initList]
    · simp [machine,gateEmbed,stackFamily,Turing.initList,h]

set_option backward.isDefEq.respectTransparency false in
/-- One charged dispatch selects the input-preserving copy or reject cleanup. -/
theorem gate_dispatch (ts : Terms) (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (answer flag : Bool) (bits : List Bool) :
    (machine ts tm ea eb).step (gateEmbed ts tm (Turing.initList tm []).stk
      (Shared.ComplexityBridge.TM2GateClean.sweepEmbed ts (Shared.ComplexityBridge.TM2GateSweep.cfg
        Shared.ComplexityBridge.TM2GateSweep.done answer flag bits (fun _ => [])))) =
      some (transferEmbed ts tm ea (Shared.ComplexityBridge.TM2GateTransfer.cfg tm ea
        (if answer then .load else .discard) none bits [] (Turing.initList tm []).stk)) := by
  cases answer <;>
    change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _) <;>
    congr 2 <;>
    simp only [gateEmbed,Shared.ComplexityBridge.TM2GateClean.sweepEmbed,Shared.ComplexityBridge.TM2GateSweep.cfg,
      transferEmbed,Shared.ComplexityBridge.TM2GateTransfer.cfg] <;>
    rw [gateStacks_empty_aux] <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem ready_dispatch (ts : Terms) (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (bits : List Bool) (v : Option Bool) :
    (machine ts tm ea eb).step (transferEmbed ts tm ea (Shared.ComplexityBridge.TM2GateTransfer.cfg tm ea
      .ready v [] [] (Turing.initList tm (bits.map ea.symm)).stk)) =
      some (checkerEmbed ts tm (fun _ => []) (Turing.initList tm (bits.map ea.symm))) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2
  funext k
  cases k with
  | inl j => cases j with
    | inl b => cases b <;> rfl
    | inr j => rfl
  | inr j => rfl

set_option backward.isDefEq.respectTransparency false in
theorem checker_halt (ts : Terms) (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (out : List (tm.Γ tm.k₁)) :
    checkerEmbed ts tm (fun _ => []) (Turing.haltList tm out) = Turing.haltList (machine ts tm ea eb) out := by
  change Cfg.mk _ _ _ = Cfg.mk _ _ _
  congr 1
  funext k
  cases k with
  | inl j => simp [checkerEmbed,stackFamily,Turing.haltList,machine]
  | inr j =>
    by_cases h : j = tm.k₁
    · subst j; simp [checkerEmbed,stackFamily,Turing.haltList,machine]
    · simp [checkerEmbed,stackFamily,Turing.haltList,machine,h]

set_option backward.isDefEq.respectTransparency false in
theorem reject_dispatch (ts : Terms) (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (v : Option Bool) :
    (machine ts tm ea eb).step (transferEmbed ts tm ea (Shared.ComplexityBridge.TM2GateTransfer.cfg tm ea
      .rejected v [] [] (Turing.initList tm []).stk)) =
      some (Turing.haltList (machine ts tm ea eb) [eb.symm false]) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2
  have he : (Turing.initList tm []).stk = fun _ => [] := by
    funext j
    by_cases hj : j = tm.k₀
    · subst j; simp [Turing.initList]
    · simp [Turing.initList,hj]
  have hz : (Shared.ComplexityBridge.TM2GateTransfer.cfg tm ea .rejected v [] [] (Turing.initList tm []).stk).stk =
      fun _ => [] := by
    rw [he]
    funext k
    cases k with
    | inl j => cases j with
      | inl b => cases b <;> rfl
      | inr j => rfl
    | inr j => rfl
  rw [hz]
  funext k
  cases k with
  | inl j => simp [Turing.haltList,machine,Function.update]
  | inr j =>
    by_cases h : j = tm.k₁
    · subst j; simp [Turing.haltList,machine,Function.update]
    · simp [Turing.haltList,machine,Function.update,h]

set_option backward.isDefEq.respectTransparency false in
/-- Combine the cleaned cutoff gate with an arbitrary Boolean-input/output
checker. The checker's full finite run and both continuations are charged. -/
theorem compose_run (ts : Terms) (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (x w : List Bool) (n : Nat) (b : Bool)
    (hcheck : runSteps tm.step n (Turing.initList tm ((BitstringEncoding.bitEncode (x,w)).map ea.symm)) =
      some (Turing.haltList tm [eb.symm b])) :
    ∃ t ≤ (Shared.ComplexityBridge.TM2GateClean.timePolynomial ts).eval
        (BitstringEncoding.bitEncode (x,w)).length + 2*(BitstringEncoding.bitEncode (x,w)).length+n+4,
      runSteps (machine ts tm ea eb).step t (Turing.initList (machine ts tm ea eb) (BitstringEncoding.bitEncode (x,w))) =
        some (Turing.haltList (machine ts tm ea eb)
          [eb.symm (if w.length ≤ Shared.Codes.NumericPolynomial.eval ts x.length then b else false)]) := by
  let bits := BitstringEncoding.bitEncode (x,w)
  let answer := if w.length ≤ Shared.Codes.NumericPolynomial.eval ts x.length then true else false
  obtain ⟨m,hm,flag,hr⟩ := Shared.ComplexityBridge.TM2GateClean.gate_clean_run ts x w
  let finished := Shared.ComplexityBridge.TM2GateClean.sweepEmbed ts
    (Shared.ComplexityBridge.TM2GateSweep.cfg Shared.ComplexityBridge.TM2GateSweep.done answer flag bits (fun _ => []))
  change runSteps (Shared.ComplexityBridge.TM2GateClean.machine ts).step m
    (Turing.initList (Shared.ComplexityBridge.TM2GateClean.machine ts) bits) = some finished at hr
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    (Shared.ComplexityBridge.TM2GateClean.machine ts).step (machine ts tm ea eb).step
    (gateEmbed ts tm (Turing.initList tm []).stk) (gateTerminal ts) (gate_stable ts)
    (gate_step ts tm ea eb (Turing.initList tm []).stk) m
    (Turing.initList (Shared.ComplexityBridge.TM2GateClean.machine ts) bits) finished (by rfl) hr
  by_cases hc : w.length ≤ Shared.Codes.NumericPolynomial.eval ts x.length
  · have hans : answer = true := by simp [answer,hc]
    let src := Shared.ComplexityBridge.TM2GateTransfer.cfg tm ea .load none bits [] (Turing.initList tm []).stk
    let dst := Shared.ComplexityBridge.TM2GateTransfer.cfg tm ea .ready none [] [] (Turing.initList tm (bits.map ea.symm)).stk
    have ht := Shared.ComplexityBridge.TM2GateTransfer.transfer_correct tm ea bits
    change runSteps (Shared.ComplexityBridge.TM2GateTransfer.machine tm ea).step (2*bits.length+2) src = some dst at ht
    obtain ⟨c,hc',hcr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
      (Shared.ComplexityBridge.TM2GateTransfer.machine tm ea).step (machine ts tm ea eb).step
      (transferEmbed ts tm ea) (transferTerminal tm ea) (transfer_stable tm ea) (transfer_step ts tm ea eb)
      (2*bits.length+2) src dst (by left; rfl) ht
    refine ⟨a+1+c+1+n,?_,?_⟩
    · dsimp [bits] at *; omega
    · simp only [hc,if_true]
      rw [initial_eq,show a+1+c+1+n = a+((c+(n+1))+1) by omega,runSteps_add,har]
      change runSteps (machine ts tm ea eb).step ((c+(n+1))+1) (gateEmbed ts tm (Turing.initList tm []).stk finished) = _
      rw [runSteps_front]
      change ((machine ts tm ea eb).step (gateEmbed ts tm (Turing.initList tm []).stk finished)).bind _ = _
      dsimp [finished]
      have hg := gate_dispatch ts tm ea eb answer flag bits
      simp only [Turing.FinTM2.step] at hg
      rw [hg,hans]
      change runSteps (machine ts tm ea eb).step (c+(n+1)) (transferEmbed ts tm ea src) = _
      rw [runSteps_add,hcr]
      change runSteps (machine ts tm ea eb).step (n+1) (transferEmbed ts tm ea dst) = _
      dsimp [dst]
      rw [runSteps_front]
      have hready := ready_dispatch ts tm ea eb bits none
      simp only [Turing.FinTM2.step] at hready
      rw [hready]
      change runSteps (machine ts tm ea eb).step n (checkerEmbed ts tm (fun _ => []) (Turing.initList tm (bits.map ea.symm))) = _
      rw [checker_run,hcheck]
      change some (checkerEmbed ts tm (fun _ => []) (Turing.haltList tm [eb.symm b])) = _
      rw [checker_halt]
  · have hans : answer = false := by simp [answer,hc]
    let src := Shared.ComplexityBridge.TM2GateTransfer.cfg tm ea .discard none bits [] (Turing.initList tm []).stk
    let dst := Shared.ComplexityBridge.TM2GateTransfer.cfg tm ea .rejected none [] [] (Turing.initList tm []).stk
    have ht := Shared.ComplexityBridge.TM2GateTransfer.discard_run tm ea bits [] (Turing.initList tm []).stk none
    change runSteps (Shared.ComplexityBridge.TM2GateTransfer.machine tm ea).step (bits.length+1) src = some dst at ht
    obtain ⟨c,hc',hcr⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
      (Shared.ComplexityBridge.TM2GateTransfer.machine tm ea).step (machine ts tm ea eb).step
      (transferEmbed ts tm ea) (transferTerminal tm ea) (transfer_stable tm ea) (transfer_step ts tm ea eb)
      (bits.length+1) src dst (by right; rfl) ht
    refine ⟨a+1+c+1,?_,?_⟩
    · dsimp [bits] at *; omega
    · simp only [hc,if_false]
      rw [initial_eq,show a+1+c+1 = a+((c+1)+1) by omega,runSteps_add,har]
      change runSteps (machine ts tm ea eb).step ((c+1)+1) (gateEmbed ts tm (Turing.initList tm []).stk finished) = _
      rw [runSteps_front]
      change ((machine ts tm ea eb).step (gateEmbed ts tm (Turing.initList tm []).stk finished)).bind _ = _
      dsimp [finished]
      have hg := gate_dispatch ts tm ea eb answer flag bits
      simp only [Turing.FinTM2.step] at hg
      rw [hg,hans]
      change runSteps (machine ts tm ea eb).step (c+1) (transferEmbed ts tm ea src) = _
      rw [show c+1 = c+1 by omega,runSteps_add,hcr]
      change (machine ts tm ea eb).step (transferEmbed ts tm ea dst) = _
      exact reject_dispatch ts tm ea eb none

def composeAux (ts : Terms) (a : Turing.TM2ComputableAux Bool Bool) : Turing.TM2ComputableAux Bool Bool where
  tm := machine ts a.tm a.inputAlphabet a.outputAlphabet
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := a.outputAlphabet

noncomputable def timePolynomial (ts : Terms) (p : Polynomial Nat) : Polynomial Nat :=
  Shared.ComplexityBridge.TM2GateClean.timePolynomial ts + Polynomial.C 2*Polynomial.X + p + Polynomial.C 4

theorem timePolynomial_eval (ts : Terms) (p : Polynomial Nat) (n : Nat) :
    (timePolynomial ts p).eval n = (Shared.ComplexityBridge.TM2GateClean.timePolynomial ts).eval n + 2*n + p.eval n + 4 := by
  simp [timePolynomial]

set_option backward.isDefEq.respectTransparency false in
/-- Original-cutoff masking preserves polynomial time in the canonical Google
model, for every fixed polynomial and every polynomial-time Boolean relation. -/
theorem cutoffMask_isPolyTime (ts : Terms) (R : (List Bool × List Bool) → Bool)
    (hR : ComplexityTheory.IsPolyTime R) :
    ComplexityTheory.IsPolyTime (Shared.ComplexityBridge.TM2PairTotalPoly.cutoffMask ts R) := by
  rcases hR with ⟨hR⟩
  let a := hR.toTM2ComputableAux
  let c := composeAux ts a
  refine ⟨{ toTM2ComputableAux := c, time := timePolynomial ts hR.time, outputsFun := ?_ }⟩
  intro pair
  rcases pair with ⟨x,w⟩
  obtain ⟨⟨n,hn⟩,hnle⟩ := hR.outputsFun (x,w)
  have hcheck : runSteps a.tm.step n
      (Turing.initList a.tm ((BitstringEncoding.bitEncode (x,w)).map a.inputAlphabet.symm)) =
        some (Turing.haltList a.tm [a.outputAlphabet.symm (R (x,w))]) := by
    rw [runSteps_iterate]
    exact hn
  let hrun := compose_run ts a.tm a.inputAlphabet a.outputAlphabet x w n (R (x,w)) hcheck
  let t := Classical.choose hrun
  have ht := (Classical.choose_spec hrun).1
  have hr := (Classical.choose_spec hrun).2
  refine ⟨⟨t,?_⟩,?_⟩
  · rw [runSteps_iterate] at hr
    change (fun o => o.bind c.tm.step)^[t]
      (some (Turing.initList c.tm ((BitstringEncoding.bitEncode (x,w)).map id))) =
        some (Turing.haltList c.tm ([Shared.ComplexityBridge.TM2PairTotalPoly.cutoffMask ts R (x,w)].map a.outputAlphabet.symm))
    simp only [List.map_id,List.map_cons,List.map_nil]
    change _ = some (Turing.haltList c.tm [a.outputAlphabet.symm
      (if w.length ≤ Shared.Codes.NumericPolynomial.eval ts x.length then R (x,w) else false)])
    exact hr
  · rw [timePolynomial_eval]
    change t ≤ (Shared.ComplexityBridge.TM2GateClean.timePolynomial ts).eval
      (BitstringEncoding.bitEncode (x,w)).length + 2*(BitstringEncoding.bitEncode (x,w)).length + hR.time.eval
      (BitstringEncoding.bitEncode (x,w)).length + 4
    change n ≤ hR.time.eval (BitstringEncoding.bitEncode (x,w)).length at hnle
    change t ≤ (Shared.ComplexityBridge.TM2GateClean.timePolynomial ts).eval
      (BitstringEncoding.bitEncode (x,w)).length + 2*(BitstringEncoding.bitEncode (x,w)).length+n+4 at ht
    omega

theorem cutoffMaskClosed : Shared.ComplexityBridge.TM2PairTotalPoly.CutoffMaskClosed :=
  cutoffMask_isPolyTime

/-- The previously conditional canonical verifier wrapper is now discharged. -/
theorem goodVerifierRelationPoly : Shared.ComplexityBridge.TM2WholePair.GoodVerifierRelationPoly :=
  Shared.ComplexityBridge.TM2PairTotalPoly.goodVerifierRelationPoly_of_cutoff cutoffMaskClosed

/-- Good verifier existence is now equivalent to canonical complement-SAT
membership in NP, without a separate cutoff-wrapper assumption. -/
theorem good_verifier_iff_complement_in_NP :
    (∃ v : Shared.NPCONP.TM2Verifier.Verifier, ∀ x, Shared.NPCONP.TM2Verifier.test v x = true) ↔
      Shared.ComplexityBridge.CNF.complementSat ∈ ComplexityTheory.NP :=
  Shared.ComplexityBridge.TM2WholePair.good_verifier_iff_complement_in_NP goodVerifierRelationPoly

/-- The separate NP/coNP beeper theorem still requires a concrete progress
certificate, SAT completeness, and canonical NP reduction closure. -/
theorem npconp_certified_conditional {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.NPCONP.TM2Verifier.compare 0 M)
    (complete : Shared.ComplexityBridge.CanonicalClasses.CompleteLanguage Shared.ComplexityBridge.CNF.sat)
    (np_pullback : Shared.ComplexityBridge.CanonicalClasses.PullbackClosed ComplexityTheory.NP) :
    M.system.EventuallySilent ↔ ComplexityTheory.NP = ComplexityTheory.coNP :=
  Shared.ComplexityBridge.TM2WholePair.npconp_certified_conditional cert complete np_pullback goodVerifierRelationPoly

namespace Fixtures
/-- A small checker which consumes its input and returns true. -/
def checker : Turing.FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m := fun _ => .pop false (fun _ h => h)
    (.branch Option.isSome (.goto (fun _ => ())) (.push true (fun _ => true) .halt))

set_option maxRecDepth 10000 in
/-- Empty input and witness pass a zero cutoff and run the checker. -/
example : (runSteps (machine [] checker (Equiv.refl Bool) (Equiv.refl Bool)).step 27
    (Turing.initList (machine [] checker (Equiv.refl Bool) (Equiv.refl Bool))
      (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool))))).map
    (fun q => (q.l.isNone,q.stk (.inr true))) = some (true,[true]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr true)))
    (runSteps (machine [] checker (Equiv.refl Bool) (Equiv.refl Bool)).step 27
      (Turing.initList (machine [] checker (Equiv.refl Bool) (Equiv.refl Bool))
        (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool))))) : Option (Bool × List Bool)) = _
  decide

set_option maxRecDepth 10000 in
/-- A one-bit witness exceeds a zero cutoff and returns false, even though
the supplied checker would return true. -/
example : (runSteps (machine [] checker (Equiv.refl Bool) (Equiv.refl Bool)).step 32
    (Turing.initList (machine [] checker (Equiv.refl Bool) (Equiv.refl Bool))
      (BitstringEncoding.bitEncode (([] : List Bool),[true])))).map
    (fun q => (q.l.isNone,q.stk (.inr true))) = some (true,[false]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr true)))
    (runSteps (machine [] checker (Equiv.refl Bool) (Equiv.refl Bool)).step 32
      (Turing.initList (machine [] checker (Equiv.refl Bool) (Equiv.refl Bool))
        (BitstringEncoding.bitEncode (([] : List Bool),[true])))) : Option (Bool × List Bool)) = _
  decide
set_option maxRecDepth 10000 in
/-- The reject path honors a nonidentity Boolean output alphabet. -/
example : (runSteps (machine [] checker Equiv.boolNot Equiv.boolNot).step 32
    (Turing.initList (machine [] checker Equiv.boolNot Equiv.boolNot)
      (BitstringEncoding.bitEncode (([] : List Bool),[true])))).map
    (fun q => (q.l.isNone,q.stk (.inr true))) = some (true,[true]) := by
  change (Option.map (fun q => (q.l.isNone,q.stk (.inr true)))
    (runSteps (machine [] checker Equiv.boolNot Equiv.boolNot).step 32
      (Turing.initList (machine [] checker Equiv.boolNot Equiv.boolNot)
        (BitstringEncoding.bitEncode (([] : List Bool),[true])))) : Option (Bool × List Bool)) = _
  decide
end Fixtures

end Shared.ComplexityBridge.TM2CutoffCompose
