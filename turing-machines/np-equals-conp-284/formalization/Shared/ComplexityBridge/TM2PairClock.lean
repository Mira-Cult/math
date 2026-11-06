import Shared.ComplexityBridge.TM2LoadedClock

namespace Shared.ComplexityBridge.TM2PairClock
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2FiniteReverse Shared.ComplexityBridge.TM2BooleanInput
abbrev Power := Shared.ComplexityBridge.TM2PairPower.machine
abbrev Runner := Shared.ComplexityBridge.TM2LoadedClock.machine
abbrev PowerKey := Shared.ComplexityBridge.TM2PairPower.K
abbrev PowerLabel (k : Nat) := Shared.ComplexityBridge.TM2PairPower.Labels k
abbrev PowerState := Option Bool × Bool
abbrev Key (ks : Nat) := PowerKey ⊕ Fin (ks+1)
abbrev Alphabet (ks symbols : Nat) : Key ks → Type
  | .inl _ => Bool
  | .inr _ => Fin (symbols+1)
abbrev Label (k : Nat) (p : Program) := PowerLabel k ⊕ Shared.ComplexityBridge.TM2LoadedClock.Label p
abbrev State (states : Nat) := PowerState ⊕ Shared.ComplexityBridge.TM2LoadedClock.State states

def powerState : State states → PowerState
  | .inl v => v
  | .inr _ => (none,false)
def powerStacks (ks symbols : Nat) (S : PowerKey → List Bool)
    (other : Fin (ks+1) → List (Fin (symbols+1))) : (s : Key ks) → List (Alphabet ks symbols s)
  | .inl j => S j
  | .inr j => other j

theorem powerStacks_update (ks symbols : Nat) (S : PowerKey → List Bool)
    (other : Fin (ks+1) → List (Fin (symbols+1))) (j : PowerKey) (xs : List Bool) :
    powerStacks ks symbols (Function.update S j xs) other = Function.update (powerStacks ks symbols S other) (.inl j) xs := by
  funext s
  cases s with
  | inl a =>
    by_cases h : a = j
    · subst a; simp [powerStacks,Function.update]
    · have hh : Sum.inl a ≠ (Sum.inl j : Key ks) := by simpa using h
      simp [powerStacks,Function.update_of_ne h,Function.update_of_ne hh]
  | inr a => simp [powerStacks,Function.update]

def liftPower (ks states symbols : Nat) (k : Nat) (p : Program) :
    Stmt (fun _ : PowerKey => Bool) (PowerLabel k) PowerState →
      Stmt (Alphabet ks symbols) (Label k p) (State states)
  | .push j f q => .push (.inl j) (fun s => f (powerState s)) (liftPower ks states symbols k p q)
  | .peek j f q => .peek (.inl j) (fun s h => .inl (f (powerState s) h)) (liftPower ks states symbols k p q)
  | .pop j f q => .pop (.inl j) (fun s h => .inl (f (powerState s) h)) (liftPower ks states symbols k p q)
  | .load f q => .load (fun s => .inl (f (powerState s))) (liftPower ks states symbols k p q)
  | .branch f q r => .branch (fun s => f (powerState s)) (liftPower ks states symbols k p q) (liftPower ks states symbols k p r)
  | .goto f => .goto (fun s => .inl (f (powerState s)))
  | .halt => .halt

def powerEmbed (ks states symbols : Nat) (k : Nat) (p : Program)
    (other : Fin (ks+1) → List (Fin (symbols+1))) (c : (Power k).Cfg) :
    Cfg (Alphabet ks symbols) (Label k p) (State states) :=
  ⟨c.l.map Sum.inl,.inl c.var,powerStacks ks symbols c.stk other⟩

set_option backward.isDefEq.respectTransparency false in
theorem liftPower_aux (ks states symbols : Nat) (k : Nat) (p : Program)
    (q : Stmt (fun _ : PowerKey => Bool) (PowerLabel k) PowerState) (v : PowerState)
    (S : PowerKey → List Bool) (other : Fin (ks+1) → List (Fin (symbols+1))) :
    stepAux (liftPower ks states symbols k p q) (.inl v) (powerStacks ks symbols S other) =
      powerEmbed ks states symbols k p other (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih (f v) S
  | push j f q ih =>
    simp only [liftPower,stepAux,powerState,powerStacks]
    rw [← powerStacks_update ks symbols S other j (f v::S j)]
    exact ih v _
  | peek j f q ih =>
    change stepAux (liftPower ks states symbols k p q) (.inl (f v (S j).head?)) (powerStacks ks symbols S other) = _
    exact ih (f v (S j).head?) S
  | pop j f q ih =>
    simp only [liftPower,stepAux,powerState,powerStacks]
    rw [← powerStacks_update ks symbols S other j (S j).tail]
    exact ih (f v (S j).head?) _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftPower,stepAux,powerState,h,ihq,ihr]

def runnerState (states initial : Nat) : State states → Shared.ComplexityBridge.TM2LoadedClock.State states
  | .inl _ => (none,clip states initial)
  | .inr v => v

def runnerKey (ks : Nat) : Shared.ComplexityBridge.TM2LoadedClock.Key ks → Key ks
  | .inl _ => .inl (.inr .a)
  | .inr (.inl false) => .inl (.inl false)
  | .inr (.inl true) => .inl (.inl true)
  | .inr (.inr j) => .inr j

def runnerStacks (ks symbols : Nat) (aux : Shared.ComplexityBridge.TM2UnaryMultiply.Stack → List Bool)
    (S : (s : Shared.ComplexityBridge.TM2LoadedClock.Key ks) →
      List (Shared.ComplexityBridge.TM2LoadedClock.Alphabet ks symbols s)) : (s : Key ks) → List (Alphabet ks symbols s)
  | .inl (.inl false) => S (.inr (.inl false))
  | .inl (.inl true) => S (.inr (.inl true))
  | .inl (.inr .a) => S (.inl ())
  | .inl (.inr j) => aux j
  | .inr j => S (.inr (.inr j))

theorem runner_update_clock (ks symbols : Nat) (aux : Shared.ComplexityBridge.TM2UnaryMultiply.Stack → List Bool)
    (S : (s : Shared.ComplexityBridge.TM2LoadedClock.Key ks) →
      List (Shared.ComplexityBridge.TM2LoadedClock.Alphabet ks symbols s)) (xs : List (Bool)) :
    runnerStacks ks symbols aux (Function.update S (.inl ()) xs) =
      Function.update (runnerStacks ks symbols aux S) (runnerKey ks (.inl ())) xs := by
  funext s
  cases s with
  | inl a =>
    cases a with
    | inl b => cases b <;> simp [runnerStacks,runnerKey,Function.update] <;> rfl
    | inr q => cases q <;> simp [runnerStacks,runnerKey,Function.update] <;> rfl
  | inr a => simp [runnerStacks,runnerKey,Function.update] <;> rfl

theorem runner_update_input (ks symbols : Nat) (aux : Shared.ComplexityBridge.TM2UnaryMultiply.Stack → List Bool)
    (S : (s : Shared.ComplexityBridge.TM2LoadedClock.Key ks) →
      List (Shared.ComplexityBridge.TM2LoadedClock.Alphabet ks symbols s)) (xs : List (Bool)) :
    runnerStacks ks symbols aux (Function.update S (.inr (.inl false)) xs) =
      Function.update (runnerStacks ks symbols aux S) (runnerKey ks (.inr (.inl false))) xs := by
  funext s
  cases s with
  | inl a =>
    cases a with
    | inl b => cases b <;> simp [runnerStacks,runnerKey,Function.update] <;> rfl
    | inr q => cases q <;> simp [runnerStacks,runnerKey,Function.update] <;> rfl
  | inr a => simp [runnerStacks,runnerKey,Function.update] <;> rfl

theorem runner_update_scratch (ks symbols : Nat) (aux : Shared.ComplexityBridge.TM2UnaryMultiply.Stack → List Bool)
    (S : (s : Shared.ComplexityBridge.TM2LoadedClock.Key ks) →
      List (Shared.ComplexityBridge.TM2LoadedClock.Alphabet ks symbols s)) (xs : List (Bool)) :
    runnerStacks ks symbols aux (Function.update S (.inr (.inl true)) xs) =
      Function.update (runnerStacks ks symbols aux S) (runnerKey ks (.inr (.inl true))) xs := by
  funext s
  cases s with
  | inl a =>
    cases a with
    | inl b => cases b <;> simp [runnerStacks,runnerKey,Function.update] <;> rfl
    | inr q => cases q <;> simp [runnerStacks,runnerKey,Function.update] <;> rfl
  | inr a => simp [runnerStacks,runnerKey,Function.update] <;> rfl

theorem runner_update_core (ks symbols : Nat) (aux : Shared.ComplexityBridge.TM2UnaryMultiply.Stack → List Bool)
    (S : (s : Shared.ComplexityBridge.TM2LoadedClock.Key ks) →
      List (Shared.ComplexityBridge.TM2LoadedClock.Alphabet ks symbols s)) (j : Fin (ks+1)) (xs : List (Fin (symbols+1))) :
    runnerStacks ks symbols aux (Function.update S (.inr (.inr j)) xs) =
      Function.update (runnerStacks ks symbols aux S) (runnerKey ks (.inr (.inr j))) xs := by
  funext s
  cases s with
  | inl a =>
    cases a with
    | inl b => cases b <;> simp [runnerStacks,runnerKey,Function.update] <;> rfl
    | inr q => cases q <;> simp [runnerStacks,runnerKey,Function.update] <;> rfl
  | inr a =>
    by_cases h : a = j
    · subst a; simp [runnerStacks,runnerKey,Function.update] <;> rfl
    · simp [runnerStacks,runnerKey,Function.update,h] <;> rfl

def liftRunner (ks states symbols initial : Nat) (k : Nat) (p : Program) :
    Stmt (Shared.ComplexityBridge.TM2LoadedClock.Alphabet ks symbols)
      (Shared.ComplexityBridge.TM2LoadedClock.Label p) (Shared.ComplexityBridge.TM2LoadedClock.State states) →
      Stmt (Alphabet ks symbols) (Label k p) (State states)
  | .push (.inl ()) f q => .push (.inl (.inr .a)) (fun v => f (runnerState states initial v)) (liftRunner ks states symbols initial k p q)
  | .push (.inr (.inl false)) f q => .push (.inl (.inl false)) (fun v => f (runnerState states initial v)) (liftRunner ks states symbols initial k p q)
  | .push (.inr (.inl true)) f q => .push (.inl (.inl true)) (fun v => f (runnerState states initial v)) (liftRunner ks states symbols initial k p q)
  | .push (.inr (.inr j)) f q => .push (.inr j) (fun v => f (runnerState states initial v)) (liftRunner ks states symbols initial k p q)
  | .peek (.inl ()) f q => .peek (.inl (.inr .a)) (fun v h => .inr (f (runnerState states initial v) h)) (liftRunner ks states symbols initial k p q)
  | .peek (.inr (.inl false)) f q => .peek (.inl (.inl false)) (fun v h => .inr (f (runnerState states initial v) h)) (liftRunner ks states symbols initial k p q)
  | .peek (.inr (.inl true)) f q => .peek (.inl (.inl true)) (fun v h => .inr (f (runnerState states initial v) h)) (liftRunner ks states symbols initial k p q)
  | .peek (.inr (.inr j)) f q => .peek (.inr j) (fun v h => .inr (f (runnerState states initial v) h)) (liftRunner ks states symbols initial k p q)
  | .pop (.inl ()) f q => .pop (.inl (.inr .a)) (fun v h => .inr (f (runnerState states initial v) h)) (liftRunner ks states symbols initial k p q)
  | .pop (.inr (.inl false)) f q => .pop (.inl (.inl false)) (fun v h => .inr (f (runnerState states initial v) h)) (liftRunner ks states symbols initial k p q)
  | .pop (.inr (.inl true)) f q => .pop (.inl (.inl true)) (fun v h => .inr (f (runnerState states initial v) h)) (liftRunner ks states symbols initial k p q)
  | .pop (.inr (.inr j)) f q => .pop (.inr j) (fun v h => .inr (f (runnerState states initial v) h)) (liftRunner ks states symbols initial k p q)
  | .load f q => .load (fun v => .inr (f (runnerState states initial v))) (liftRunner ks states symbols initial k p q)
  | .branch f q r => .branch (fun v => f (runnerState states initial v))
      (liftRunner ks states symbols initial k p q) (liftRunner ks states symbols initial k p r)
  | .goto f => .goto (fun v => .inr (f (runnerState states initial v)))
  | .halt => .halt

def runnerEmbed (ks states symbols : Nat) (k : Nat) (p : Program)
    (aux : Shared.ComplexityBridge.TM2UnaryMultiply.Stack → List Bool)
    (c : (Runner ks states symbols p 0 0 0 0 0 0).Cfg) :
    Cfg (Alphabet ks symbols) (Label k p) (State states) :=
  ⟨c.l.map Sum.inr,.inr c.var,runnerStacks ks symbols aux c.stk⟩

set_option backward.isDefEq.respectTransparency false in
theorem liftRunner_aux (ks states symbols initial : Nat) (k : Nat) (p : Program)
    (q : Stmt (Shared.ComplexityBridge.TM2LoadedClock.Alphabet ks symbols)
      (Shared.ComplexityBridge.TM2LoadedClock.Label p) (Shared.ComplexityBridge.TM2LoadedClock.State states))
    (v : Shared.ComplexityBridge.TM2LoadedClock.State states)
    (aux : Shared.ComplexityBridge.TM2UnaryMultiply.Stack → List Bool)
    (S : (s : Shared.ComplexityBridge.TM2LoadedClock.Key ks) →
      List (Shared.ComplexityBridge.TM2LoadedClock.Alphabet ks symbols s)) :
    stepAux (liftRunner ks states symbols initial k p q) (.inr v) (runnerStacks ks symbols aux S) =
      runnerEmbed ks states symbols k p aux (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih (f v) S
  | push s f q ih =>
    cases s with
    | inl u =>
      cases u
      simp only [liftRunner,stepAux,runnerState,runnerStacks]
      have hu := runner_update_clock ks symbols aux S (f v::S (.inl ()))
      simp only [runnerKey] at hu
      rw [← hu]
      exact ih v _
    | inr s =>
      cases s with
      | inl b =>
        cases b with
        | false =>
          simp only [liftRunner,stepAux,runnerState,runnerStacks]
          have hu := runner_update_input ks symbols aux S (f v::S (.inr (.inl false)))
          simp only [runnerKey] at hu
          rw [← hu]
          exact ih v _
        | true =>
          simp only [liftRunner,stepAux,runnerState,runnerStacks]
          have hu := runner_update_scratch ks symbols aux S (f v::S (.inr (.inl true)))
          simp only [runnerKey] at hu
          rw [← hu]
          exact ih v _
      | inr j =>
        simp only [liftRunner,stepAux,runnerState,runnerStacks]
        have hu := runner_update_core ks symbols aux S j (f v::S (.inr (.inr j)))
        simp only [runnerKey] at hu
        rw [← hu]
        exact ih v _
  | peek s f q ih =>
    cases s with
    | inl u =>
      cases u
      simp only [liftRunner,stepAux,runnerState,runnerStacks]
      exact ih (f v (S (.inl ())).head?) S
    | inr s =>
      cases s with
      | inl b =>
        cases b with
        | false =>
          simp only [liftRunner,stepAux,runnerState,runnerStacks]
          exact ih (f v (S (.inr (.inl false))).head?) S
        | true =>
          simp only [liftRunner,stepAux,runnerState,runnerStacks]
          exact ih (f v (S (.inr (.inl true))).head?) S
      | inr j =>
        simp only [liftRunner,stepAux,runnerState,runnerStacks]
        exact ih (f v (S (.inr (.inr j))).head?) S
  | pop s f q ih =>
    cases s with
    | inl u =>
      cases u
      simp only [liftRunner,stepAux,runnerState,runnerStacks]
      have hu := runner_update_clock ks symbols aux S (S (.inl ())).tail
      simp only [runnerKey] at hu
      rw [← hu]
      exact ih (f v (S (.inl ())).head?) _
    | inr s =>
      cases s with
      | inl b =>
        cases b with
        | false =>
          simp only [liftRunner,stepAux,runnerState,runnerStacks]
          have hu := runner_update_input ks symbols aux S (S (.inr (.inl false))).tail
          simp only [runnerKey] at hu
          rw [← hu]
          exact ih (f v (S (.inr (.inl false))).head?) _
        | true =>
          simp only [liftRunner,stepAux,runnerState,runnerStacks]
          have hu := runner_update_scratch ks symbols aux S (S (.inr (.inl true))).tail
          simp only [runnerKey] at hu
          rw [← hu]
          exact ih (f v (S (.inr (.inl true))).head?) _
      | inr j =>
        simp only [liftRunner,stepAux,runnerState,runnerStacks]
        have hu := runner_update_core ks symbols aux S j (S (.inr (.inr j))).tail
        simp only [runnerKey] at hu
        rw [← hu]
        exact ih (f v (S (.inr (.inr j))).head?) _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftRunner,stepAux,runnerState,h,ihq,ihr]

def finishLabel (k : Nat) : PowerLabel k :=
  .inr (Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.index k k (by omega), .inl .outer)

def program (ks states symbols initial k : Nat) (p : Program) (input main z o : Nat) :
    Label k p → Stmt (Alphabet ks symbols) (Label k p) (State states)
  | .inl l => if l = finishLabel k then
      .load (fun _ => .inr (none,clip states initial)) (.goto (fun _ => .inr (.inl .scan)))
    else liftPower ks states symbols k p (Shared.ComplexityBridge.TM2PairPower.program k l)
  | .inr l => liftRunner ks states symbols initial k p
      (Shared.ComplexityBridge.TM2LoadedClock.program ks states symbols p input main z o l)

def machine (ks states symbols : Nat) (k : Nat) (p : Program) (input output main initial z o : Nat) : Turing.FinTM2 where
  K := Key ks
  k₀ := .inl (.inl false)
  k₁ := .inr (clip ks output)
  Γ := Alphabet ks symbols
  Λ := Label k p
  main := .inl (.inl .start)
  σ := State states
  initialState := .inl (none,false)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program ks states symbols initial k p input main z o

def powerTerminal (k : Nat) (c : (Power k).Cfg) : Prop := c.l = some (finishLabel k)
noncomputable instance (k : Nat) : DecidablePred (powerTerminal k) := fun _ => Classical.propDecidable _

theorem power_stable (k : Nat) (c : (Power k).Cfg) (h : powerTerminal k c) :
    (Power k).step c = some c := by
  cases c with
  | mk l v S =>
    change l = some (finishLabel k) at h
    subst l
    change some (stepAux (Shared.ComplexityBridge.TM2PairPower.program k (finishLabel k)) v S) = _
    simp [Shared.ComplexityBridge.TM2PairPower.program, finishLabel,
      Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.program,
      Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.index,
      Shared.ComplexityBridge.TM2PairPower.liftPower,stepAux]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem power_step (ks states symbols : Nat) (k : Nat) (p : Program) (input output main initial z o : Nat)
    (other : Fin (ks+1) → List (Fin (symbols+1))) (c : (Power k).Cfg) (h : ¬ powerTerminal k c) :
    (machine ks states symbols k p input output main initial z o).step (powerEmbed ks states symbols k p other c) =
      ((Power k).step c).map (powerEmbed ks states symbols k p other) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      have hl : l ≠ finishLabel k := by intro hl; apply h; exact congrArg some hl
      change some (stepAux (program ks states symbols initial k p input main z o (.inl l)) (.inl v)
        (powerStacks ks symbols S other)) = _
      simp only [program, if_neg hl]
      rw [liftPower_aux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem runner_step (ks states symbols : Nat) (k : Nat) (p : Program) (input output main initial z o : Nat)
    (aux : Shared.ComplexityBridge.TM2UnaryMultiply.Stack → List Bool)
    (c : (Runner ks states symbols p input output main initial z o).Cfg) :
    (machine ks states symbols k p input output main initial z o).step (runnerEmbed ks states symbols k p aux c) =
      ((Runner ks states symbols p input output main initial z o).step c).map (runnerEmbed ks states symbols k p aux) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftRunner ks states symbols initial k p
        (Shared.ComplexityBridge.TM2LoadedClock.program ks states symbols p input main z o l))
          (.inr v) (runnerStacks ks symbols aux S)) = _
      rw [liftRunner_aux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem runner_run (ks states symbols : Nat) (k : Nat) (p : Program) (input output main initial z o : Nat)
    (aux : Shared.ComplexityBridge.TM2UnaryMultiply.Stack → List Bool)
    (c : (Runner ks states symbols p input output main initial z o).Cfg) (n : Nat) :
    runSteps (machine ks states symbols k p input output main initial z o).step n (runnerEmbed ks states symbols k p aux c) =
      (runSteps (Runner ks states symbols p input output main initial z o).step n c).map
        (runnerEmbed ks states symbols k p aux) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front, runSteps_front, runner_step]
    cases h : (Runner ks states symbols p input output main initial z o).step c with
    | none => rfl
    | some c' => exact ih c'

theorem initial_eq (ks states symbols : Nat) (k : Nat) (p : Program) (input output main initial z o : Nat)
    (bits : List Bool) :
    Turing.initList (machine ks states symbols k p input output main initial z o) bits =
      powerEmbed ks states symbols k p (fun _ => []) (Turing.initList (Power k) bits) := by
  change (Cfg.mk (some (Sum.inl (Sum.inl TM2PairLength.Label.start))) (.inl (none,false)) _ :
    (machine ks states symbols k p input output main initial z o).Cfg) = _
  congr 1
  funext s
  cases s with
  | inl a =>
    cases a with
    | inl b => cases b <;> simp [machine, Power, TM2PairPower.machine, powerEmbed, powerStacks] <;> rfl
    | inr a => cases a <;> simp [machine, Power, TM2PairPower.machine, powerEmbed, powerStacks, Turing.initList, Function.update]
  | inr a => simp [machine, Power, TM2PairPower.machine, powerEmbed, powerStacks]

def aux (b : Nat) : Shared.ComplexityBridge.TM2UnaryMultiply.Stack → List Bool :=
  Shared.ComplexityBridge.TM2UnaryMultiply.stackVals 0 b 0 0 0

def runnerStart (d : InputData) (p : Program) (ticks bits : List Bool) :
    (Runner d.stackCount d.states d.symbols p d.inputStack 0 d.main d.initialState d.falseSymbol d.trueSymbol).Cfg :=
  Shared.ComplexityBridge.TM2LoadedClock.loaderEmbed d.stackCount d.states d.symbols d.inputStack p ticks
    (fun _ => []) (clip d.states d.initialState)
    (Turing.initList (Shared.ComplexityBridge.TM2Loader.loader d.symbols d.falseSymbol d.trueSymbol) bits)

set_option backward.isDefEq.respectTransparency false in
/-- The generated ticks remain on the same physical stack at the handoff;
the canonical input remains in the input stack, and numeric stacks are empty. -/
theorem dispatch (d : InputData) (k : Nat) (p : Program) (output : Nat) (bits : List Bool) (b : Nat) :
    (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol).step
      (powerEmbed d.stackCount d.states d.symbols k p (fun _ => [])
        (Shared.ComplexityBridge.TM2PairPower.powerCfg bits [] none
          (Shared.ComplexityBridge.TM2PairPower.powerFinished k b))) =
    some (runnerEmbed d.stackCount d.states d.symbols k p (aux b)
      (runnerStart d p (List.replicate (b^k) true) bits)) := by
  change some (stepAux (program d.stackCount d.states d.symbols d.initialState k p d.inputStack d.main
    d.falseSymbol d.trueSymbol (.inl (finishLabel k))) (.inl (none,false))
    (powerStacks d.stackCount d.symbols
      (Shared.ComplexityBridge.TM2PairPower.powerCfg bits [] none
        (Shared.ComplexityBridge.TM2PairPower.powerFinished k b)).stk (fun _ => []))) = _
  simp only [program, ite_true, stepAux]
  congr 1
  congr 1
  funext s
  cases s with
  | inl t =>
    cases t with
    | inl v => cases v <;> simp [powerStacks,runnerEmbed,runnerStacks,runnerStart,aux,
        Shared.ComplexityBridge.TM2PairPower.powerCfg,Shared.ComplexityBridge.TM2PairPower.powerFinished,
        Shared.ComplexityBridge.TM2PairPower.powerStacks,Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.mulEmbed,
        Shared.ComplexityBridge.TM2UnaryProductPhase.embed,Shared.ComplexityBridge.TM2UnaryMultiply.cfg,
        Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,Shared.ComplexityBridge.TM2LoadedClock.loaderEmbed,
        Shared.ComplexityBridge.TM2LoadedClock.loaderStacks, Turing.initList, TM2Loader.loader, Function.update] <;> rfl
    | inr q => cases q <;> simp [powerStacks,runnerEmbed,runnerStacks,runnerStart,aux,
        Shared.ComplexityBridge.TM2PairPower.powerCfg,Shared.ComplexityBridge.TM2PairPower.powerFinished,
        Shared.ComplexityBridge.TM2PairPower.powerStacks,Shared.ComplexityBridge.TM2UnaryProductPhase.FixedPower.mulEmbed,
        Shared.ComplexityBridge.TM2UnaryProductPhase.embed,Shared.ComplexityBridge.TM2UnaryMultiply.cfg,
        Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,Shared.ComplexityBridge.TM2LoadedClock.loaderEmbed,
        Shared.ComplexityBridge.TM2LoadedClock.loaderStacks, Turing.initList, TM2Loader.loader, Function.update] <;> rfl
  | inr j =>
    by_cases hj : j = clip d.stackCount d.inputStack
    · subst j; simp [powerStacks,runnerEmbed,runnerStacks,runnerStart,aux,
        Shared.ComplexityBridge.TM2LoadedClock.loaderEmbed,Shared.ComplexityBridge.TM2LoadedClock.loaderStacks,
        Turing.initList, TM2Loader.loader, Function.update] <;> rfl
    · simp [powerStacks,runnerEmbed,runnerStacks,runnerStart,aux,
        Shared.ComplexityBridge.TM2LoadedClock.loaderEmbed,Shared.ComplexityBridge.TM2LoadedClock.loaderStacks,
        Turing.initList, TM2Loader.loader, Function.update,hj] <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- Starting from the canonical pair input, the unified machine constructs
the clock, dispatches, and reaches the input loader. -/
theorem pair_to_runner (d : InputData) (k : Nat) (p : Program) (output : Nat) (x w : List Bool) :
    ∃ n ≤ 2*(BitstringEncoding.bitEncode (x,w)).length+5 + k*14*(x.length+w.length+4)^k,
      runSteps (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState
        d.falseSymbol d.trueSymbol).step n
        (Turing.initList (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState
          d.falseSymbol d.trueSymbol) (BitstringEncoding.bitEncode (x,w))) =
      some (runnerEmbed d.stackCount d.states d.symbols k p (aux (x.length+w.length+2))
        (runnerStart d p (List.replicate ((x.length+w.length+2)^k) true) (BitstringEncoding.bitEncode (x,w)))) := by
  let bits := BitstringEncoding.bitEncode (x,w)
  let b := x.length+w.length+2
  letI : DecidablePred (powerTerminal k) := fun _ => Classical.propDecidable _
  obtain ⟨m, hm, h⟩ := TM2UnaryTransfer.run_to_stable_lift
    (Power k).step (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState
      d.falseSymbol d.trueSymbol).step
    (powerEmbed d.stackCount d.states d.symbols k p (fun _ => [])) (powerTerminal k)
    (power_stable k) (power_step d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState
      d.falseSymbol d.trueSymbol (fun _ => [])) _
    (Turing.initList (Power k) bits)
    (Shared.ComplexityBridge.TM2PairPower.powerCfg bits [] none (Shared.ComplexityBridge.TM2PairPower.powerFinished k b))
    (by rfl) (Classical.choose_spec (Shared.ComplexityBridge.TM2PairPower.pair_power k x w)).2
  have hp : Classical.choose (Shared.ComplexityBridge.TM2PairPower.pair_power k x w) ≤
      2*bits.length+3+1+k*14*(x.length+w.length+4)^k :=
    (Classical.choose_spec (Shared.ComplexityBridge.TM2PairPower.pair_power k x w)).1
  dsimp [bits] at hp
  refine ⟨m+1, by omega, ?_⟩
  rw [initial_eq,runSteps_add,h]
  change (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol).step (powerEmbed d.stackCount d.states d.symbols k p (fun _ => [])
      (Shared.ComplexityBridge.TM2PairPower.powerCfg bits [] none (Shared.ComplexityBridge.TM2PairPower.powerFinished k b))) = _
  exact dispatch d k p output bits b

set_option backward.isDefEq.respectTransparency false in
/-- On a numeric timeout the unified finite machine constructs its exact
input-dependent clock, loads the input, executes all permitted core blocks,
and reaches the distinct timeout label. -/
theorem pair_numeric_timeout (d : InputData) (k : Nat) (p : Program) (output : Nat) (x w : List Bool)
    (hdata : validInputData d = true) (hp : programValid p d.stackCount d.states d.symbols = true)
    (start result : Shared.Codes.TM2StatementExecution.Result)
    (hstart : buildStart d (BitstringEncoding.bitEncode (x,w)) = some start)
    (hvalid : Shared.Codes.TM2StatementValidation.resultValid d.stackCount d.states d.symbols p.length start)
    (hrun : run p ((x.length+w.length+2)^k) start = .timeout result) :
    ∃ n ≤ 4*(BitstringEncoding.bitEncode (x,w)).length+9 + k*14*(x.length+w.length+4)^k + (x.length+w.length+2)^k,
      ∃ c', CfgRel d.stackCount d.states d.symbols p.length c' (Shared.Codes.TM2StatementExecution.erase result) ∧
      runSteps (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol).step n
        (Turing.initList (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol)
          (BitstringEncoding.bitEncode (x,w))) =
      some (runnerEmbed d.stackCount d.states d.symbols k p (aux (x.length+w.length+2))
        (TM2LoadedClock.clockEmbed d.stackCount d.states d.symbols p []
          (TM2UnaryClock.timeoutCfg d.stackCount d.states d.symbols p.length c'))) := by
  let bits := BitstringEncoding.bitEncode (x,w)
  let b := x.length+w.length+2
  let fuel := b^k
  obtain ⟨m, hm, hsetup⟩ := pair_to_runner d k p output x w
  obtain ⟨t, ht, c', hc, hr⟩ := TM2LoadedClock.loaded_numeric_timeout d p output fuel bits hdata hp start result hstart hvalid hrun
  have hr' := runner_run d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol (aux b) (runnerStart d p (List.replicate fuel true) bits) t
  change runSteps (Runner d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol).step t (runnerStart d p (List.replicate fuel true) bits) = _ at hr
  rw [hr] at hr'
  refine ⟨m+t, by dsimp [bits,b,fuel] at *; omega, c', hc, ?_⟩
  rw [runSteps_add,hsetup]
  exact hr'

set_option backward.isDefEq.respectTransparency false in
/-- If the bounded numeric evaluator halts, the unified machine reaches the
same halted result with all unused ticks represented. -/
theorem pair_numeric_halt (d : InputData) (k : Nat) (p : Program) (output : Nat) (x w : List Bool)
    (hdata : validInputData d = true) (hp : programValid p d.stackCount d.states d.symbols = true)
    (start result : Shared.Codes.TM2StatementExecution.Result)
    (hstart : buildStart d (BitstringEncoding.bitEncode (x,w)) = some start)
    (hvalid : Shared.Codes.TM2StatementValidation.resultValid d.stackCount d.states d.symbols p.length start)
    (hrun : run p ((x.length+w.length+2)^k) start = .halted result) :
    ∃ n ≤ 4*(BitstringEncoding.bitEncode (x,w)).length+8 + k*14*(x.length+w.length+4)^k + (x.length+w.length+2)^k,
      ∃ m ≤ (x.length+w.length+2)^k, ∃ c' flag,
        CfgRel d.stackCount d.states d.symbols p.length c' (Shared.Codes.TM2StatementExecution.erase result) ∧ c'.l = none ∧
      runSteps (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol).step n
        (Turing.initList (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol)
          (BitstringEncoding.bitEncode (x,w))) =
      some (runnerEmbed d.stackCount d.states d.symbols k p (aux (x.length+w.length+2))
        (TM2LoadedClock.clockEmbed d.stackCount d.states d.symbols p []
          (TM2UnaryClock.embed d.stackCount d.states d.symbols p.length flag
            ((List.replicate ((x.length+w.length+2)^k) true).drop m) c'))) := by
  let bits := BitstringEncoding.bitEncode (x,w)
  let b := x.length+w.length+2
  let fuel := b^k
  obtain ⟨a, ha, hsetup⟩ := pair_to_runner d k p output x w
  obtain ⟨t, ht, m, hm, c', flag, hc, hh, hr⟩ :=
    TM2LoadedClock.loaded_numeric_halt d p output fuel bits hdata hp start result hstart hvalid hrun
  have hr' := runner_run d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol (aux b) (runnerStart d p (List.replicate fuel true) bits) t
  change runSteps (Runner d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol).step t (runnerStart d p (List.replicate fuel true) bits) = _ at hr
  rw [hr] at hr'
  refine ⟨a+t, by dsimp [bits,b,fuel] at *; omega, m, hm, c', flag, hc, hh, ?_⟩
  rw [runSteps_add,hsetup]
  exact hr'

set_option backward.isDefEq.respectTransparency false in
/-- Every validated numeric candidate reaches a genuine halt or the explicit
timeout label from the canonical pair input, with a polynomial whole-block
bound for its fixed exponent. -/
theorem pair_clock_progress (d : InputData) (k : Nat) (p : Program) (output : Nat) (x w : List Bool)
    (hdata : validInputData d = true) (hmain : d.main < p.length)
    (hp : programValid p d.stackCount d.states d.symbols = true) :
    ∃ start, buildStart d (BitstringEncoding.bitEncode (x,w)) = some start ∧
    ∃ n ≤ 4*(BitstringEncoding.bitEncode (x,w)).length+9 + k*14*(x.length+w.length+4)^k + (x.length+w.length+2)^k,
      ∃ c, runSteps (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol).step n
        (Turing.initList (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol)
          (BitstringEncoding.bitEncode (x,w))) = some c ∧
        (c.l = none ∨ c.l = some (.inr (.inr (.inl false)))) := by
  let bits := BitstringEncoding.bitEncode (x,w)
  let fuel := (x.length+w.length+2)^k
  obtain ⟨start, hs, hv⟩ := Shared.ComplexityBridge.TM2FiniteBoundary.buildStart_valid d bits p hdata hmain
  refine ⟨start, hs, ?_⟩
  have hsafe := Shared.Codes.TM2Program.run_safe p d.stackCount d.states d.symbols hp fuel start hv
  cases hr : run p fuel start with
  | invalid =>
    rw [hr] at hsafe
    contradiction
  | timeout r =>
    obtain ⟨n, hn, c', hc, hrun⟩ := pair_numeric_timeout d k p output x w hdata hp start r hs hv hr
    refine ⟨n,hn,_,hrun,Or.inr ?_⟩
    rfl
  | halted r =>
    obtain ⟨n, hn, m, hm, c', flag, hc, hh, hrun⟩ := pair_numeric_halt d k p output x w hdata hp start r hs hv hr
    refine ⟨n,by omega,_,hrun,Or.inl ?_⟩
    simp [runnerEmbed, TM2LoadedClock.clockEmbed, TM2UnaryClock.embed, TM2Combined.embedCfg, hh]

/-- Empty pair, exponent zero: the only permitted core block halts exactly
at the clock boundary after the input-driven initialization. -/
example : (runSteps (machine 1 1 2 0 [.halt] 0 0 0 0 0 1).step 13
    (Turing.initList (machine 1 1 2 0 [.halt] 0 0 0 0 0 1)
      (BitstringEncoding.bitEncode (([] : List Bool), ([] : List Bool))))).map (fun c => c.l.isNone) = some true := by
  change (Option.map (fun c => c.l.isNone) (runSteps (machine 1 1 2 0 [.halt] 0 0 0 0 0 1).step 13
    (Turing.initList (machine 1 1 2 0 [.halt] 0 0 0 0 0 1)
      (BitstringEncoding.bitEncode (([] : List Bool), ([] : List Bool))))) : Option Bool) = some true
  decide

/-- One permitted loop block followed by timeout at the distinct timeout label. -/
example : (runSteps (machine 1 1 2 0 [.goto [0]] 0 0 0 0 0 1).step 14
    (Turing.initList (machine 1 1 2 0 [.goto [0]] 0 0 0 0 0 1)
      (BitstringEncoding.bitEncode (([] : List Bool), ([] : List Bool))))).map
      (fun c => match c.l with | some (.inr (.inr (.inl false))) => true | _ => false) = some true := by
  change (Option.map (fun c => match c.l with | some (.inr (.inr (.inl false))) => true | _ => false)
    (runSteps (machine 1 1 2 0 [.goto [0]] 0 0 0 0 0 1).step 14
      (Turing.initList (machine 1 1 2 0 [.goto [0]] 0 0 0 0 0 1)
        (BitstringEncoding.bitEncode (([] : List Bool), ([] : List Bool))))) : Option Bool) = some true
  decide

end Shared.ComplexityBridge.TM2PairClock
