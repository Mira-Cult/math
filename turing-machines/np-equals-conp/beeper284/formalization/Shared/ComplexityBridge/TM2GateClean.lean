import Shared.ComplexityBridge.TM2GenericStackBound

set_option linter.unusedSimpArgs false
namespace Shared.ComplexityBridge.TM2GateClean
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
abbrev Terms := Shared.Codes.NumericPolynomial.Terms
abbrev Key := Shared.ComplexityBridge.TM2CutoffGate.Key
abbrev Label (ts : Terms) := Shared.ComplexityBridge.TM2CutoffGate.Label ts ⊕ Shared.ComplexityBridge.TM2GateSweep.Phase
abbrev State := Shared.ComplexityBridge.TM2CutoffGate.State ⊕ (Bool × Bool)

def gateState : State → Shared.ComplexityBridge.TM2CutoffGate.State | .inl s => s | .inr _ => .inl none
def sweepState : State → Bool × Bool | .inl _ => (false,false) | .inr s => s

def gateEmbed (ts : Terms) (q : (Shared.ComplexityBridge.TM2CutoffGate.machine ts).Cfg) : Cfg (fun _ : Key => Bool) (Label ts) State :=
  ⟨q.l.map Sum.inl,.inl q.var,q.stk⟩
def sweepEmbed (ts : Terms) (q : Shared.ComplexityBridge.TM2GateSweep.machine.Cfg) : Cfg (fun _ : Key => Bool) (Label ts) State :=
  ⟨q.l.map Sum.inr,.inr q.var,q.stk⟩

def liftGate (ts : Terms) : Stmt (fun _ : Key => Bool) (Shared.ComplexityBridge.TM2CutoffGate.Label ts) Shared.ComplexityBridge.TM2CutoffGate.State →
    Stmt (fun _ : Key => Bool) (Label ts) State
  | .push j f q => .push j (fun v => f (gateState v)) (liftGate ts q)
  | .peek j f q => .peek j (fun v h => .inl (f (gateState v) h)) (liftGate ts q)
  | .pop j f q => .pop j (fun v h => .inl (f (gateState v) h)) (liftGate ts q)
  | .load f q => .load (fun v => .inl (f (gateState v))) (liftGate ts q)
  | .branch f q r => .branch (fun v => f (gateState v)) (liftGate ts q) (liftGate ts r)
  | .goto f => .goto (fun v => .inl (f (gateState v)))
  | .halt => .halt

def liftSweep (ts : Terms) : Stmt (fun _ : Key => Bool) Shared.ComplexityBridge.TM2GateSweep.Phase (Bool × Bool) →
    Stmt (fun _ : Key => Bool) (Label ts) State
  | .push j f q => .push j (fun v => f (sweepState v)) (liftSweep ts q)
  | .peek j f q => .peek j (fun v h => .inr (f (sweepState v) h)) (liftSweep ts q)
  | .pop j f q => .pop j (fun v h => .inr (f (sweepState v) h)) (liftSweep ts q)
  | .load f q => .load (fun v => .inr (f (sweepState v))) (liftSweep ts q)
  | .branch f q r => .branch (fun v => f (sweepState v)) (liftSweep ts q) (liftSweep ts r)
  | .goto f => .goto (fun v => .inr (f (sweepState v)))
  | .halt => .halt

theorem liftGate_aux (ts : Terms) (q : Stmt (fun _ : Key => Bool) (Shared.ComplexityBridge.TM2CutoffGate.Label ts) Shared.ComplexityBridge.TM2CutoffGate.State)
    (v : Shared.ComplexityBridge.TM2CutoffGate.State) (S : Key → List Bool) :
    stepAux (liftGate ts q) (.inl v) S = gateEmbed ts (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih => exact ih _ _
  | push j f q ih => exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftGate,stepAux,gateState,h,ihq,ihr]

theorem liftSweep_aux (ts : Terms) (q : Stmt (fun _ : Key => Bool) Shared.ComplexityBridge.TM2GateSweep.Phase (Bool × Bool))
    (v : Bool × Bool) (S : Key → List Bool) :
    stepAux (liftSweep ts q) (.inr v) S = sweepEmbed ts (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih _ _
  | peek j f q ih => exact ih _ _
  | pop j f q ih => exact ih _ _
  | push j f q ih => exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftSweep,stepAux,sweepState,h,ihq,ihr]

def ready : Shared.ComplexityBridge.TM2CutoffGate.State → Bool | .inl _ => false | .inr _ => true

def dispatch (ts : Terms) (b : Bool) (l : Shared.ComplexityBridge.TM2CutoffGate.Label ts) : Stmt (fun _ : Key => Bool) (Label ts) State :=
  .branch (fun v => ready (gateState v))
    (.load (fun _ => .inr (b,false)) (.goto (fun _ => .inr ⟨0,by decide⟩)))
    (liftGate ts (Shared.ComplexityBridge.TM2CutoffGate.program ts l))

def program (ts : Terms) : Label ts → Stmt (fun _ : Key => Bool) (Label ts) State
  | .inl (.inr (.inr .accept)) => dispatch ts true (.inr (.inr .accept))
  | .inl (.inr (.inr .reject)) => dispatch ts false (.inr (.inr .reject))
  | .inl l => liftGate ts (Shared.ComplexityBridge.TM2CutoffGate.program ts l)
  | .inr l => liftSweep ts (Shared.ComplexityBridge.TM2GateSweep.program l)

def machine (ts : Terms) : Turing.FinTM2 where
  K := Key
  k₀ := .inl false
  k₁ := .inl true
  Γ := fun _ => Bool
  Λ := Label ts
  main := .inl (.inl .start)
  σ := State
  initialState := .inl (.inl none)
  m := program ts

def terminal (ts : Terms) (q : (Shared.ComplexityBridge.TM2CutoffGate.machine ts).Cfg) : Prop :=
  (q.l = some (.inr (.inr .accept)) ∨ q.l = some (.inr (.inr .reject))) ∧ ∃ b, q.var = .inr b
noncomputable instance (ts : Terms) : DecidablePred (terminal ts) := fun _ => Classical.propDecidable _

set_option backward.isDefEq.respectTransparency false in
theorem gate_stable (ts : Terms) (q : (Shared.ComplexityBridge.TM2CutoffGate.machine ts).Cfg) (h : terminal ts q) :
    (Shared.ComplexityBridge.TM2CutoffGate.machine ts).step q = some q := by
  cases q with
  | mk l v S =>
    rcases h with ⟨hl,⟨b,hv⟩⟩
    change v = .inr b at hv
    change l = some (.inr (.inr .accept)) ∨ l = some (.inr (.inr .reject)) at hl
    subst v
    rcases hl with hl | hl <;> subst l <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem gate_step (ts : Terms) (q : (Shared.ComplexityBridge.TM2CutoffGate.machine ts).Cfg) (h : ¬ terminal ts q) :
    (machine ts).step (gateEmbed ts q) = ((Shared.ComplexityBridge.TM2CutoffGate.machine ts).step q).map (gateEmbed ts) := by
  cases q with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | inl a =>
        change some (stepAux (liftGate ts (Shared.ComplexityBridge.TM2CutoffGate.program ts (.inl a))) (.inl v) S) = _
        rw [liftGate_aux]; rfl
      | inr a => cases a with
        | inl a =>
          change some (stepAux (liftGate ts (Shared.ComplexityBridge.TM2CutoffGate.program ts (.inr (.inl a)))) (.inl v) S) = _
          rw [liftGate_aux]; rfl
        | inr a => cases a with
          | compare =>
            change some (stepAux (liftGate ts (Shared.ComplexityBridge.TM2CutoffGate.program ts (.inr (.inr .compare)))) (.inl v) S) = _
            rw [liftGate_aux]; rfl
          | accept | reject =>
            cases v with
            | inl o =>
              change some (stepAux (liftGate ts (Shared.ComplexityBridge.TM2CutoffGate.program ts _)) (.inl (.inl o)) S) = _
              rw [liftGate_aux]; rfl
            | inr b => exact False.elim (h ⟨by simp,⟨b,rfl⟩⟩)

set_option backward.isDefEq.respectTransparency false in
theorem sweep_step (ts : Terms) (q : Shared.ComplexityBridge.TM2GateSweep.machine.Cfg) :
    (machine ts).step (sweepEmbed ts q) = (Shared.ComplexityBridge.TM2GateSweep.machine.step q).map (sweepEmbed ts) := by
  cases q with
  | mk l v S => cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftSweep ts (Shared.ComplexityBridge.TM2GateSweep.program l)) (.inr v) S) = _
      rw [liftSweep_aux]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem sweep_run (ts : Terms) (q : Shared.ComplexityBridge.TM2GateSweep.machine.Cfg) (n : Nat) :
    runSteps (machine ts).step n (sweepEmbed ts q) = (runSteps Shared.ComplexityBridge.TM2GateSweep.machine.step n q).map (sweepEmbed ts) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front,runSteps_front,sweep_step]
    cases h : Shared.ComplexityBridge.TM2GateSweep.machine.step q with
    | none => rfl
    | some q' => exact ih q'

theorem initial_eq (ts : Terms) (bits : List Bool) :
    Turing.initList (machine ts) bits = gateEmbed ts (Turing.initList (Shared.ComplexityBridge.TM2CutoffGate.machine ts) bits) := by
  rfl

def finalGate (ts : Terms) (x w : List Bool) (remaining : Nat) : (Shared.ComplexityBridge.TM2CutoffGate.machine ts).Cfg :=
  Shared.ComplexityBridge.TM2CutoffGate.compareEmbed ts
    (Shared.ComplexityBridge.TM2CutoffGate.afterPoly ts (BitstringEncoding.bitEncode (x,w)) x.length w.length)
    (if w.length ≤ Shared.Codes.NumericPolynomial.eval ts x.length then
      Shared.ComplexityBridge.TM2UnaryCutoff.cfg .accept false 0 remaining
    else Shared.ComplexityBridge.TM2UnaryCutoff.cfg .reject false remaining 0)

theorem finalGate_input (ts : Terms) (x w : List Bool) (remaining : Nat) :
    (finalGate ts x w remaining).stk (.inl false) = BitstringEncoding.bitEncode (x,w) := by
  unfold finalGate
  split <;> rfl

theorem finalGate_terminal (ts : Terms) (x w : List Bool) (remaining : Nat) :
    terminal ts (finalGate ts x w remaining) := by
  unfold finalGate terminal
  split
  · constructor
    · left; rfl
    · exact ⟨false,rfl⟩
  · constructor
    · right; rfl
    · exact ⟨false,rfl⟩

theorem gate_dispatch (ts : Terms) (b flag : Bool) (S : Key → List Bool) :
    (machine ts).step (gateEmbed ts ⟨some (.inr (.inr (if b then .accept else .reject))),.inr flag,S⟩) =
      some (sweepEmbed ts ⟨some ⟨0,by decide⟩,(b,false),S⟩) := by
  cases b <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem finalGate_dispatch (ts : Terms) (x w : List Bool) (remaining : Nat) :
    (machine ts).step (gateEmbed ts (finalGate ts x w remaining)) =
      some (sweepEmbed ts (Shared.ComplexityBridge.TM2GateSweep.cfg ⟨0,by decide⟩
        (if w.length ≤ Shared.Codes.NumericPolynomial.eval ts x.length then true else false) false
        (BitstringEncoding.bitEncode (x,w))
        (fun i => (finalGate ts x w remaining).stk (Shared.ComplexityBridge.TM2GateSweep.auxKey i)))) := by
  have he := Shared.ComplexityBridge.TM2GateSweep.stackVals_eta (finalGate ts x w remaining).stk
  rw [finalGate_input] at he
  unfold finalGate at he ⊢
  by_cases h : w.length ≤ Shared.Codes.NumericPolynomial.eval ts x.length <;>
    simp only [h,if_true,if_false] at he ⊢ <;>
    change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _) <;>
    congr 2 <;> exact he.symm

noncomputable def timePolynomial (ts : Terms) : Polynomial Nat :=
  let p := Shared.ComplexityBridge.TM2CutoffGate.timePolynomial ts
  p + Polynomial.C 1 + Polynomial.C 9 * (Polynomial.X + p *
    Polynomial.C (Shared.ComplexityBridge.TM2GenericStackBound.tableBound (Shared.ComplexityBridge.TM2CutoffGate.machine ts)) + Polynomial.C 1)

set_option backward.isDefEq.respectTransparency false in
/-- The real input-driven gate and all nine charged cleanup phases form one
finite TM2. The input and its decision bit survive; every other stack is empty. -/
theorem gate_clean_run (ts : Terms) (x w : List Bool) :
    ∃ t ≤ (timePolynomial ts).eval (BitstringEncoding.bitEncode (x,w)).length, ∃ flag,
      runSteps (machine ts).step t (Turing.initList (machine ts) (BitstringEncoding.bitEncode (x,w))) =
        some (sweepEmbed ts (Shared.ComplexityBridge.TM2GateSweep.cfg Shared.ComplexityBridge.TM2GateSweep.done
          (if w.length ≤ Shared.Codes.NumericPolynomial.eval ts x.length then true else false) flag
          (BitstringEncoding.bitEncode (x,w)) (fun _ => []))) := by
  let bits := BitstringEncoding.bitEncode (x,w)
  let p := (Shared.ComplexityBridge.TM2CutoffGate.timePolynomial ts).eval bits.length
  let D := Shared.ComplexityBridge.TM2GenericStackBound.tableBound (Shared.ComplexityBridge.TM2CutoffGate.machine ts)
  obtain ⟨n,hn,r,hr⟩ := Shared.ComplexityBridge.TM2CutoffGate.gate_polynomial_bound ts x w
  change n ≤ p at hn
  change runSteps (Shared.ComplexityBridge.TM2CutoffGate.machine ts).step n
    (Turing.initList (Shared.ComplexityBridge.TM2CutoffGate.machine ts) bits) = some (finalGate ts x w r) at hr
  obtain ⟨a,ha,har⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    (Shared.ComplexityBridge.TM2CutoffGate.machine ts).step (machine ts).step (gateEmbed ts) (terminal ts)
    (gate_stable ts) (gate_step ts) n (Turing.initList (Shared.ComplexityBridge.TM2CutoffGate.machine ts) bits)
    (finalGate ts x w r) (finalGate_terminal ts x w r) hr
  let A := fun i => (finalGate ts x w r).stk (Shared.ComplexityBridge.TM2GateSweep.auxKey i)
  have hA : ∀ i, (A i).length ≤ bits.length + p*D := by
    intro i
    have hstack := Shared.ComplexityBridge.TM2GenericStackBound.run_from_input_length
      (Shared.ComplexityBridge.TM2CutoffGate.machine ts) bits n (finalGate ts x w r) hr
      (Shared.ComplexityBridge.TM2GateSweep.auxKey i)
    have hmul : n*D ≤ p*D := Nat.mul_le_mul_right D hn
    dsimp [A,D] at *
    omega
  obtain ⟨b,hb,flag,hbr⟩ := Shared.ComplexityBridge.TM2GateSweep.sweep_from_start
    (if w.length ≤ Shared.Codes.NumericPolynomial.eval ts x.length then true else false) false bits A
    (bits.length+p*D) hA
  have hb' := sweep_run ts (Shared.ComplexityBridge.TM2GateSweep.cfg ⟨0,by decide⟩
    (if w.length ≤ Shared.Codes.NumericPolynomial.eval ts x.length then true else false) false bits A) b
  rw [hbr] at hb'
  refine ⟨a+1+b,?_,flag,?_⟩
  · change a+1+b ≤ (timePolynomial ts).eval bits.length
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    change a+1+b ≤ p+1+9*(bits.length+p*D+1)
    omega
  · rw [initial_eq,show a+1+b = a+(b+1) by omega,runSteps_add,har]
    change runSteps (machine ts).step (b+1) (gateEmbed ts (finalGate ts x w r)) = _
    rw [runSteps_front,finalGate_dispatch]
    change runSteps (machine ts).step b (sweepEmbed ts (Shared.ComplexityBridge.TM2GateSweep.cfg ⟨0,by decide⟩
      (if w.length ≤ Shared.Codes.NumericPolynomial.eval ts x.length then true else false) false bits A)) = _
    exact hb'

end Shared.ComplexityBridge.TM2GateClean
