import Shared.ComplexityBridge.TM2BitstringFinish

/-! One finite TM2 loads the real input, executes a validated numeric program,
transfers its entire Boolean output, clears all other stacks, resets state,
and reaches the library's exact halt configuration. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2BitstringWhole
open Turing.TM2 Shared.ComplexityBridge.TM2Combined Shared.ComplexityBridge.TM2Symbols
open Shared.Codes.TM2Program

abbrev RLabel (p : Program) := Bool ⊕ Fin (p.length+1)
abbrev RState (states : Nat) := Option Bool × Fin (states+1)
abbrev FLabel (ks : Nat) := Shared.ComplexityBridge.TM2BitstringFinish.Label ks
abbrev FState (symbols : Nat) := Shared.ComplexityBridge.TM2BitstringFinish.State symbols
abbrev Label (ks : Nat) (p : Program) := Unit ⊕ (RLabel p ⊕ FLabel ks)
abbrev State (states symbols : Nat) := RState states ⊕ FState symbols
abbrev RStmt (ks states symbols : Nat) (p : Program) :=
  Stmt (Alphabet ks symbols) (RLabel p) (RState states)
abbrev FStmt (ks symbols : Nat) := Stmt (Alphabet ks symbols) (FLabel ks) (FState symbols)

def rState (states symbols initial : Nat) : State states symbols → RState states
  | .inl v => v | .inr _ => (none,Shared.ComplexityBridge.TM2FiniteReverse.clip states initial)
def fState (states symbols : Nat) : State states symbols → FState symbols
  | .inl _ => .inl (none,none) | .inr v => v

def liftRun (ks states symbols initial : Nat) (p : Program) : RStmt ks states symbols p →
    Stmt (Alphabet ks symbols) (Label ks p) (State states symbols)
  | .push k f q => .push k (fun s => f (rState states symbols initial s)) (liftRun ks states symbols initial p q)
  | .peek k f q => .peek k (fun s x => .inl (f (rState states symbols initial s) x)) (liftRun ks states symbols initial p q)
  | .pop k f q => .pop k (fun s x => .inl (f (rState states symbols initial s) x)) (liftRun ks states symbols initial p q)
  | .load f q => .load (fun s => .inl (f (rState states symbols initial s))) (liftRun ks states symbols initial p q)
  | .branch f a b => .branch (fun s => f (rState states symbols initial s))
      (liftRun ks states symbols initial p a) (liftRun ks states symbols initial p b)
  | .goto f => .goto (fun s => .inr (.inl (f (rState states symbols initial s))))
  | .halt => .load (fun _ => .inr (.inl (none,none))) (.goto (fun _ => .inr (.inr (.inl .scan))))

def liftFinish (ks states symbols : Nat) (p : Program) : FStmt ks symbols →
    Stmt (Alphabet ks symbols) (Label ks p) (State states symbols)
  | .push k f q => .push k (fun s => f (fState states symbols s)) (liftFinish ks states symbols p q)
  | .peek k f q => .peek k (fun s x => .inr (f (fState states symbols s) x)) (liftFinish ks states symbols p q)
  | .pop k f q => .pop k (fun s x => .inr (f (fState states symbols s) x)) (liftFinish ks states symbols p q)
  | .load f q => .load (fun s => .inr (f (fState states symbols s))) (liftFinish ks states symbols p q)
  | .branch f a b => .branch (fun s => f (fState states symbols s))
      (liftFinish ks states symbols p a) (liftFinish ks states symbols p b)
  | .goto f => .goto (fun s => .inr (.inr (f (fState states symbols s))))
  | .halt => .load (fun _ => .inr (.inl (none,none))) .halt

def program (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat) :
    Label ks p → Stmt (Alphabet ks symbols) (Label ks p) (State states symbols)
  | .inl () => .load (fun _ => .inl (none,Shared.ComplexityBridge.TM2FiniteReverse.clip states initial))
      (.goto (fun _ => .inr (.inl (.inl false))))
  | .inr (.inl l) => liftRun ks states symbols initial p
      (Shared.ComplexityBridge.TM2Combined.program ks states symbols p input main z inOne l)
  | .inr (.inr l) => liftFinish ks states symbols p
      (Shared.ComplexityBridge.TM2BitstringFinish.program ks symbols output one l)

def machine (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat) : Turing.FinTM2 where
  K := Bool ⊕ Fin (ks+1)
  k₀ := .inl false
  k₁ := .inl true
  Γ := Alphabet ks symbols
  Λ := Label ks p
  main := .inl ()
  σ := State states symbols
  initialState := .inr (.inl (none,none))
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program ks states symbols p input output main initial z inOne one

def runEmbed (ks states symbols : Nat) (p : Program)
    (c : Cfg (Alphabet ks symbols) (RLabel p) (RState states)) :
    Cfg (Alphabet ks symbols) (Label ks p) (State states symbols) :=
  match c.l with
  | some l => ⟨some (.inr (.inl l)),.inl c.var,c.stk⟩
  | none => ⟨some (.inr (.inr (.inl .scan))),.inr (.inl (none,none)),c.stk⟩

def finishEmbed (ks states symbols : Nat) (p : Program)
    (c : Cfg (Alphabet ks symbols) (FLabel ks) (FState symbols)) :
    Cfg (Alphabet ks symbols) (Label ks p) (State states symbols) :=
  match c.l with
  | some l => ⟨some (.inr (.inr l)),.inr c.var,c.stk⟩
  | none => ⟨none,.inr (.inl (none,none)),c.stk⟩

theorem liftRun_stepAux (ks states symbols initial : Nat) (p : Program) (q : RStmt ks states symbols p)
    (v : RState states) (S : (k : Bool ⊕ Fin (ks+1)) → List (Alphabet ks symbols k)) :
    stepAux (liftRun ks states symbols initial p q) (.inl v) S = runEmbed ks states symbols p (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | push k f q ih => exact ih v _
  | peek k f q ih => exact ih _ S
  | pop k f q ih => exact ih _ _
  | load f q ih => exact ih _ S
  | branch f a b iha ihb => by_cases h : f v <;> simp [liftRun,stepAux,rState,h,iha,ihb]

theorem liftFinish_stepAux (ks states symbols : Nat) (p : Program) (q : FStmt ks symbols)
    (v : FState symbols) (S : (k : Bool ⊕ Fin (ks+1)) → List (Alphabet ks symbols k)) :
    stepAux (liftFinish ks states symbols p q) (.inr v) S = finishEmbed ks states symbols p (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | push k f q ih => exact ih v _
  | peek k f q ih => exact ih _ S
  | pop k f q ih => exact ih _ _
  | load f q ih => exact ih _ S
  | branch f a b iha ihb => by_cases h : f v <;> simp [liftFinish,stepAux,fState,h,iha,ihb]

theorem run_step (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (c : (Shared.ComplexityBridge.TM2Combined.machine ks states symbols p input output main initial z inOne).Cfg)
    (hactive : c.l ≠ none) :
    (machine ks states symbols p input output main initial z inOne one).step (runEmbed ks states symbols p c) =
      ((Shared.ComplexityBridge.TM2Combined.machine ks states symbols p input output main initial z inOne).step c).map
        (runEmbed ks states symbols p) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => contradiction
    | some l =>
      change some (stepAux (liftRun ks states symbols initial p
        (Shared.ComplexityBridge.TM2Combined.program ks states symbols p input main z inOne l)) (.inl v) S) = _
      rw [liftRun_stepAux]
      rfl

theorem run_sim (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat) (n : Nat)
    (c d : (Shared.ComplexityBridge.TM2Combined.machine ks states symbols p input output main initial z inOne).Cfg)
    (h : runSteps (Shared.ComplexityBridge.TM2Combined.machine ks states symbols p input output main initial z inOne).step n c = some d) :
    runSteps (machine ks states symbols p input output main initial z inOne one).step n (runEmbed ks states symbols p c) =
      some (runEmbed ks states symbols p d) := by
  induction n generalizing c with
  | zero => change some c = some d at h; cases h; rfl
  | succ n ih =>
    rw [runSteps_front] at h
    cases hs : (Shared.ComplexityBridge.TM2Combined.machine ks states symbols p input output main initial z inOne).step c with
    | none => rw [hs] at h; contradiction
    | some c' =>
      have ha : c.l ≠ none := by
        intro hl
        have hn : (Shared.ComplexityBridge.TM2Combined.machine ks states symbols p input output main initial z inOne).step c = none := by
          cases c with
          | mk l v S => cases l with | none => rfl | some l => simp at hl
        rw [hn] at hs
        contradiction
      have hh : runSteps (Shared.ComplexityBridge.TM2Combined.machine ks states symbols p input output main initial z inOne).step n c' = some d := by
        rw [hs] at h; exact h
      rw [runSteps_front,run_step ks states symbols p input output main initial z inOne one c ha,hs]
      exact ih c' hh

theorem finish_step (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (c : (Shared.ComplexityBridge.TM2BitstringFinish.machine ks symbols output one).Cfg) :
    (machine ks states symbols p input output main initial z inOne one).step (finishEmbed ks states symbols p c) =
      ((Shared.ComplexityBridge.TM2BitstringFinish.machine ks symbols output one).step c).map
        (finishEmbed ks states symbols p) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftFinish ks states symbols p
        (Shared.ComplexityBridge.TM2BitstringFinish.program ks symbols output one l)) (.inr v) S) = _
      rw [liftFinish_stepAux]
      rfl

theorem finish_sim (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat) (n : Nat)
    (c : (Shared.ComplexityBridge.TM2BitstringFinish.machine ks symbols output one).Cfg) :
    runSteps (machine ks states symbols p input output main initial z inOne one).step n (finishEmbed ks states symbols p c) =
      (runSteps (Shared.ComplexityBridge.TM2BitstringFinish.machine ks symbols output one).step n c).map
        (finishEmbed ks states symbols p) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front,runSteps_front,finish_step]
    cases h : (Shared.ComplexityBridge.TM2BitstringFinish.machine ks symbols output one).step c with
    | none => rfl
    | some c' => exact ih c'

theorem startup (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat)
    (bits : List Bool) :
    (machine ks states symbols p input output main initial z inOne one).step
      (Turing.initList (machine ks states symbols p input output main initial z inOne one) bits) =
    some (runEmbed ks states symbols p
      (Turing.initList (Shared.ComplexityBridge.TM2Combined.machine ks states symbols p input output main initial z inOne) bits)) := by
  rfl

theorem handoff (ks states symbols : Nat) (p : Program) (input output main initial one : Nat)
    (c : (Shared.ComplexityBridge.TM2FiniteReverse.finiteCore ks states symbols p input output main initial).Cfg)
    (hl : c.l = none) :
    runEmbed ks states symbols p (embedCfg ks states symbols p.length none [] [] c) =
      finishEmbed ks states symbols p (Shared.ComplexityBridge.TM2BitstringFinish.transferEmbed ks symbols
        (Shared.ComplexityBridge.TM2BitstringTransfer.cfg ks symbols output one (some .scan) (none,none) [] [] c.stk)) := by
  simp [runEmbed,embedCfg,hl,Shared.ComplexityBridge.TM2BitstringFinish.transferEmbed,
    Shared.ComplexityBridge.TM2BitstringTransfer.cfg,finishEmbed]

theorem halt_embed (ks states symbols : Nat) (p : Program) (input output main initial z inOne one : Nat) (bits : List Bool) :
    finishEmbed ks states symbols p (Turing.haltList (Shared.ComplexityBridge.TM2BitstringFinish.machine ks symbols output one) bits) =
      Turing.haltList (machine ks states symbols p input output main initial z inOne one) bits := by
  change (Cfg.mk (none : Option (Label ks p)) (.inr (.inl (none,none)) : State states symbols) _ :
    (machine ks states symbols p input output main initial z inOne one).Cfg) = _
  congr 1

/-- A validated halted numeric run is implemented by one finite TM2 from the
actual input to the canonical full-output halt, with a polynomial expression
in the input length, fuel and fixed program depth. -/
theorem run_to_halt
    (d : Shared.ComplexityBridge.TM2BooleanInput.InputData)
    (p : Shared.Codes.TM2Program.Program) (output z one : Nat) (input : List Bool) (fuel : Nat)
    (start r : Shared.Codes.TM2StatementExecution.Result) (bits : List Bool)
    (hdata : Shared.ComplexityBridge.TM2BooleanInput.validInputData d = true) (hmain : d.main < p.length)
    (hp : Shared.Codes.TM2Program.programValid p d.stackCount d.states d.symbols = true)
    (hstart : Shared.ComplexityBridge.TM2BooleanInput.buildStart d input = some start)
    (hrun : Shared.Codes.TM2Program.run p fuel start = .halted r)
    (he : Shared.ComplexityBridge.TM2BitstringOutput.extractMemory (z,one,output,r.label,r.memory) = some bits) :
    let bound := input.length + fuel * Shared.ComplexityBridge.TM2StackBound.programDepth p
    ∃ t ≤ 1+(2*input.length+2+fuel)+(2*bound+2+(d.stackCount+1)*(bound+1)+1),
      runSteps (machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
        d.falseSymbol d.trueSymbol one).step t
        (Turing.initList (machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
          d.falseSymbol d.trueSymbol one) input) =
      some (Turing.haltList (machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
        d.falseSymbol d.trueSymbol one) bits) := by
  obtain ⟨n,hn,c',hload,hl,t,ht,hfinish⟩ :=
    Shared.ComplexityBridge.TM2BitstringFinish.loaded_numeric_then_finish d p output z one input fuel
      start r bits hdata hmain hp hstart hrun he
  have hsim := run_sim d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol one (2*input.length+2+n)
    (Turing.initList (Shared.ComplexityBridge.TM2Combined.machine d.stackCount d.states d.symbols p
      d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol) input)
    (embedCfg d.stackCount d.states d.symbols p.length none [] [] c') hload
  rw [handoff d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState one c' hl] at hsim
  have hfsim := finish_sim d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol one t
    (Shared.ComplexityBridge.TM2BitstringFinish.transferEmbed d.stackCount d.symbols
      (Shared.ComplexityBridge.TM2BitstringTransfer.cfg d.stackCount d.symbols output one
        (some .scan) (none,none) [] [] c'.stk))
  rw [hfinish] at hfsim
  simp only [Option.map_some] at hfsim
  rw [halt_embed] at hfsim
  refine ⟨1+(2*input.length+2+n)+t,by omega,?_⟩
  rw [show 1+(2*input.length+2+n)+t = ((2*input.length+2+n)+t)+1 by omega,runSteps_front,startup]
  simp only [Option.bind_some]
  rw [runSteps_add,hsim]
  exact hfsim

end Shared.ComplexityBridge.TM2BitstringWhole
