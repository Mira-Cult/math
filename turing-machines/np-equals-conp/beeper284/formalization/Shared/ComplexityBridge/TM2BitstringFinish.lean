import Shared.ComplexityBridge.TM2BitstringCleanup

/-! A single finite TM2 performs numeric-output transfer and then sweeps all
remaining numeric stacks, preserving the entire Boolean output. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2BitstringFinish
open Turing.TM2 Shared.ComplexityBridge.TM2Combined Shared.ComplexityBridge.TM2Symbols
open Shared.Codes.TM2Program

abbrev TState (symbols : Nat) := Shared.ComplexityBridge.TM2BitstringTransfer.State symbols
abbrev Label (ks : Nat) := Shared.ComplexityBridge.TM2BitstringTransfer.Label ⊕ Fin (ks+2)
abbrev State (symbols : Nat) := TState symbols ⊕ Bool
abbrev TStmt (ks symbols : Nat) := Stmt (Alphabet ks symbols) Shared.ComplexityBridge.TM2BitstringTransfer.Label (TState symbols)
abbrev CStmt (ks symbols : Nat) := Stmt (Alphabet ks symbols) (Fin (ks+2)) Bool

def tState {symbols : Nat} : State symbols → TState symbols
  | .inl v => v | .inr _ => (none,none)
def cState {symbols : Nat} : State symbols → Bool
  | .inl _ => false | .inr v => v

def liftTransfer (ks symbols : Nat) : TStmt ks symbols → Stmt (Alphabet ks symbols) (Label ks) (State symbols)
  | .push k f q => .push k (fun s => f (tState s)) (liftTransfer ks symbols q)
  | .peek k f q => .peek k (fun s x => .inl (f (tState s) x)) (liftTransfer ks symbols q)
  | .pop k f q => .pop k (fun s x => .inl (f (tState s) x)) (liftTransfer ks symbols q)
  | .load f q => .load (fun s => .inl (f (tState s))) (liftTransfer ks symbols q)
  | .branch f a b => .branch (fun s => f (tState s)) (liftTransfer ks symbols a) (liftTransfer ks symbols b)
  | .goto f => .goto (fun s => .inl (f (tState s)))
  | .halt => .load (fun _ => .inr false) (.goto (fun _ => .inr ⟨0,by omega⟩))

def liftCleanup (ks symbols : Nat) : CStmt ks symbols → Stmt (Alphabet ks symbols) (Label ks) (State symbols)
  | .push k f q => .push k (fun s => f (cState s)) (liftCleanup ks symbols q)
  | .peek k f q => .peek k (fun s x => .inr (f (cState s) x)) (liftCleanup ks symbols q)
  | .pop k f q => .pop k (fun s x => .inr (f (cState s) x)) (liftCleanup ks symbols q)
  | .load f q => .load (fun s => .inr (f (cState s))) (liftCleanup ks symbols q)
  | .branch f a b => .branch (fun s => f (cState s)) (liftCleanup ks symbols a) (liftCleanup ks symbols b)
  | .goto f => .goto (fun s => .inr (f (cState s)))
  | .halt => .load (fun _ => .inl (none,none)) .halt

def program (ks symbols output one : Nat) : Label ks → Stmt (Alphabet ks symbols) (Label ks) (State symbols)
  | .inl l => liftTransfer ks symbols (Shared.ComplexityBridge.TM2BitstringTransfer.program ks symbols output one l)
  | .inr l => liftCleanup ks symbols (Shared.ComplexityBridge.TM2BitstringCleanup.program ks symbols l)

def machine (ks symbols output one : Nat) : Turing.FinTM2 where
  K := Bool ⊕ Fin (ks+1)
  k₀ := .inl false
  k₁ := .inl true
  Γ := Alphabet ks symbols
  Λ := Label ks
  main := .inl .scan
  σ := State symbols
  initialState := .inl (none,none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program ks symbols output one

def transferEmbed (ks symbols : Nat)
    (c : Cfg (Alphabet ks symbols) Shared.ComplexityBridge.TM2BitstringTransfer.Label (TState symbols)) :
    Cfg (Alphabet ks symbols) (Label ks) (State symbols) :=
  match c.l with
  | some l => ⟨some (.inl l),.inl c.var,c.stk⟩
  | none => ⟨some (.inr ⟨0,by omega⟩),.inr false,c.stk⟩

def cleanupEmbed (ks symbols : Nat) (c : Cfg (Alphabet ks symbols) (Fin (ks+2)) Bool) :
    Cfg (Alphabet ks symbols) (Label ks) (State symbols) :=
  match c.l with
  | some l => ⟨some (.inr l),.inr c.var,c.stk⟩
  | none => ⟨none,.inl (none,none),c.stk⟩

theorem liftTransfer_stepAux (ks symbols : Nat) (q : TStmt ks symbols) (v : TState symbols)
    (S : (k : Bool ⊕ Fin (ks+1)) → List (Alphabet ks symbols k)) :
    stepAux (liftTransfer ks symbols q) (.inl v) S = transferEmbed ks symbols (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | push k f q ih => exact ih v _
  | peek k f q ih => exact ih _ S
  | pop k f q ih => exact ih _ _
  | load f q ih => exact ih _ S
  | branch f a b iha ihb => by_cases h : f v <;> simp [liftTransfer,stepAux,tState,h,iha,ihb]

theorem liftCleanup_stepAux (ks symbols : Nat) (q : CStmt ks symbols) (v : Bool)
    (S : (k : Bool ⊕ Fin (ks+1)) → List (Alphabet ks symbols k)) :
    stepAux (liftCleanup ks symbols q) (.inr v) S = cleanupEmbed ks symbols (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | push k f q ih => exact ih v _
  | peek k f q ih => exact ih _ S
  | pop k f q ih => exact ih _ _
  | load f q ih => exact ih _ S
  | branch f a b iha ihb => by_cases h : f v <;> simp [liftCleanup,stepAux,cState,h,iha,ihb]

theorem transfer_step (ks symbols output one : Nat)
    (c : (Shared.ComplexityBridge.TM2BitstringTransfer.machine ks symbols output one).Cfg) (hactive : c.l ≠ none) :
    (machine ks symbols output one).step (transferEmbed ks symbols c) =
      ((Shared.ComplexityBridge.TM2BitstringTransfer.machine ks symbols output one).step c).map
        (transferEmbed ks symbols) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => contradiction
    | some l =>
      change some (stepAux (liftTransfer ks symbols
        (Shared.ComplexityBridge.TM2BitstringTransfer.program ks symbols output one l)) (.inl v) S) = _
      rw [liftTransfer_stepAux]
      rfl

/-- The transfer machine's final halt is redirected to cleanup in the same
block, without changing any stack. -/
theorem transfer_run (ks symbols output one : Nat) (n : Nat)
    (c d : (Shared.ComplexityBridge.TM2BitstringTransfer.machine ks symbols output one).Cfg)
    (h : runSteps (Shared.ComplexityBridge.TM2BitstringTransfer.machine ks symbols output one).step n c = some d) :
    runSteps (machine ks symbols output one).step n (transferEmbed ks symbols c) =
      some (transferEmbed ks symbols d) := by
  induction n generalizing c with
  | zero => change some c = some d at h; cases h; rfl
  | succ n ih =>
    rw [runSteps_front] at h
    cases hs : (Shared.ComplexityBridge.TM2BitstringTransfer.machine ks symbols output one).step c with
    | none => rw [hs] at h; contradiction
    | some c' =>
      have ha : c.l ≠ none := by
        intro hl
        have hn : (Shared.ComplexityBridge.TM2BitstringTransfer.machine ks symbols output one).step c = none := by
          cases c with
          | mk l v S => cases l with | none => rfl | some l => simp at hl
        rw [hn] at hs
        contradiction
      have hh : runSteps (Shared.ComplexityBridge.TM2BitstringTransfer.machine ks symbols output one).step n c' = some d := by
        rw [hs] at h; exact h
      rw [runSteps_front,transfer_step ks symbols output one c ha,hs]
      exact ih c' hh

theorem cleanup_step (ks symbols output one : Nat)
    (c : (Shared.ComplexityBridge.TM2BitstringCleanup.machine ks symbols).Cfg) :
    (machine ks symbols output one).step (cleanupEmbed ks symbols c) =
      ((Shared.ComplexityBridge.TM2BitstringCleanup.machine ks symbols).step c).map (cleanupEmbed ks symbols) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftCleanup ks symbols (Shared.ComplexityBridge.TM2BitstringCleanup.program ks symbols l)) (.inr v) S) = _
      rw [liftCleanup_stepAux]
      rfl

theorem cleanup_run (ks symbols output one : Nat) (n : Nat)
    (c : (Shared.ComplexityBridge.TM2BitstringCleanup.machine ks symbols).Cfg) :
    runSteps (machine ks symbols output one).step n (cleanupEmbed ks symbols c) =
      (runSteps (Shared.ComplexityBridge.TM2BitstringCleanup.machine ks symbols).step n c).map
        (cleanupEmbed ks symbols) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front,runSteps_front,cleanup_step]
    cases h : (Shared.ComplexityBridge.TM2BitstringCleanup.machine ks symbols).step c with
    | none => rfl
    | some c' => exact ih c'

theorem handoff (ks symbols output one : Nat) (bits : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    transferEmbed ks symbols (Shared.ComplexityBridge.TM2BitstringTransfer.cfg ks symbols output one
      none (none,none) [] bits S) =
    cleanupEmbed ks symbols (Shared.ComplexityBridge.TM2BitstringCleanup.cfg ks symbols
      ⟨0,by omega⟩ false bits S) := rfl

theorem halt_embed (ks symbols output one : Nat) (bits : List Bool) :
    cleanupEmbed ks symbols (Turing.haltList (Shared.ComplexityBridge.TM2BitstringCleanup.machine ks symbols) bits) =
      Turing.haltList (machine ks symbols output one) bits := by
  change (Cfg.mk (none : Option (Label ks)) (.inl (none,none) : State symbols) _ :
    (machine ks symbols output one).Cfg) = _
  congr 1

/-- A single finite run transfers the complete bitstring, clears every core
stack, resets state, and reaches the canonical halt configuration. -/
theorem finish (ks symbols output z one : Nat) (xs : List (Fin (symbols+1)))
    (S : Fin (ks+1) → List (Fin (symbols+1))) (v : TState symbols) (bits : List Bool)
    (hdecode : Shared.ComplexityBridge.TM2BitstringOutput.decodeStack (z,one,xs.map Fin.val) = some bits)
    (bound : Nat) (hbound : ∀ k, (S k).length ≤ bound) (hx : xs.length ≤ bound) :
    ∃ t ≤ 2*bound+2+(ks+1)*(bound+1)+1,
      runSteps (machine ks symbols output one).step t
        (transferEmbed ks symbols (Shared.ComplexityBridge.TM2BitstringTransfer.cfg ks symbols output one
          (some .scan) v [] [] (Function.update S (Shared.ComplexityBridge.TM2BitstringTransfer.sourceIndex ks output) xs))) =
        some (Turing.haltList (machine ks symbols output one) bits) := by
  let S' := Function.update S (Shared.ComplexityBridge.TM2BitstringTransfer.sourceIndex ks output) []
  have hbound' : ∀ k, (S' k).length ≤ bound := by
    intro k
    by_cases h : k = Shared.ComplexityBridge.TM2BitstringTransfer.sourceIndex ks output
    · subst k; simp [S']
    · simpa [S',Function.update_of_ne h] using hbound k
  obtain ⟨t,ht,hclean⟩ := Shared.ComplexityBridge.TM2BitstringCleanup.sweep_all ks symbols bits S' false bound hbound'
  have htransfer := Shared.ComplexityBridge.TM2BitstringTransfer.transfer_decoded ks symbols output z one xs S v bits hdecode
  have htsim := transfer_run ks symbols output one (2*xs.length+2) _ _ htransfer
  rw [handoff] at htsim
  have hcsim := cleanup_run ks symbols output one t
    (Shared.ComplexityBridge.TM2BitstringCleanup.cfg ks symbols ⟨0,by omega⟩ false bits S')
  rw [hclean] at hcsim
  simp only [Option.map_some] at hcsim
  rw [halt_embed] at hcsim
  refine ⟨2*xs.length+2+t,by omega,?_⟩
  rw [runSteps_add,htsim]
  exact hcsim

/-- A validated numeric execution from the actual encoded input and the
combined output-finishing machine both have explicit finite runs. Their
inter-machine handoff is stated, not yet compiled into one table. -/
theorem loaded_numeric_then_finish
    (d : Shared.ComplexityBridge.TM2BooleanInput.InputData)
    (p : Shared.Codes.TM2Program.Program) (output z one : Nat) (input : List Bool) (fuel : Nat)
    (start r : Shared.Codes.TM2StatementExecution.Result) (bits : List Bool)
    (hdata : Shared.ComplexityBridge.TM2BooleanInput.validInputData d = true) (hmain : d.main < p.length)
    (hp : Shared.Codes.TM2Program.programValid p d.stackCount d.states d.symbols = true)
    (hstart : Shared.ComplexityBridge.TM2BooleanInput.buildStart d input = some start)
    (hrun : Shared.Codes.TM2Program.run p fuel start = .halted r)
    (he : Shared.ComplexityBridge.TM2BitstringOutput.extractMemory (z,one,output,r.label,r.memory) = some bits) :
    ∃ n ≤ fuel, ∃ c',
      runSteps (Shared.ComplexityBridge.TM2Combined.machine d.stackCount d.states d.symbols p
        d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol).step (2*input.length+2+n)
        (Turing.initList (Shared.ComplexityBridge.TM2Combined.machine d.stackCount d.states d.symbols p
          d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol) input) =
        some (embedCfg d.stackCount d.states d.symbols p.length none [] [] c') ∧
      c'.l = none ∧
      let bound := input.length + fuel * Shared.ComplexityBridge.TM2StackBound.programDepth p
      ∃ t ≤ 2*bound+2+(d.stackCount+1)*(bound+1)+1,
        runSteps (machine d.stackCount d.symbols output one).step t
          (transferEmbed d.stackCount d.symbols
            (Shared.ComplexityBridge.TM2BitstringTransfer.cfg d.stackCount d.symbols output one
              (some .scan) (none,none) [] [] c'.stk)) =
        some (Turing.haltList (machine d.stackCount d.symbols output one) bits) := by
  obtain ⟨start',hs,hv⟩ := Shared.ComplexityBridge.TM2FiniteBoundary.buildStart_valid d input p hdata hmain
  have heq : start' = start := by rw [hstart] at hs; exact Option.some.inj hs.symm
  subst start'
  have hrvalid := Shared.Codes.TM2Program.run_safe p d.stackCount d.states d.symbols hp fuel start hv
  rw [hrun] at hrvalid
  have hcore := Shared.ComplexityBridge.TM2FiniteReverse.finite_run_from_config
    d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState hp fuel start hv
  rw [hrun] at hcore
  obtain ⟨n,hn,c',hsteps,hrel,hhalt⟩ := hcore
  have hout := Shared.ComplexityBridge.TM2BitstringTransfer.extract_from_related r c' hrvalid.1 hrel bits he
  have hstack := Shared.ComplexityBridge.TM2StackBound.run_from_input_bound d input p fuel start hstart
  rw [hrun] at hstack
  let bound := input.length + fuel * Shared.ComplexityBridge.TM2StackBound.programDepth p
  have hbound := Shared.ComplexityBridge.TM2StackBound.related_stack_bound d.stackCount d.states d.symbols p.length
    c' r hrel bound hstack
  let xs := c'.stk (Shared.ComplexityBridge.TM2FiniteReverse.clip d.stackCount output)
  obtain ⟨t,ht,hfinish⟩ := finish d.stackCount d.symbols output z one xs c'.stk (none,none) bits
    hout.2 bound hbound (hbound (Shared.ComplexityBridge.TM2FiniteReverse.clip d.stackCount output))
  have hup : Function.update c'.stk (Shared.ComplexityBridge.TM2BitstringTransfer.sourceIndex d.stackCount output) xs = c'.stk :=
    Function.update_eq_self _ _
  rw [hup] at hfinish
  obtain ⟨start',hs',hload⟩ := Shared.ComplexityBridge.TM2Combined.combined_load_numeric d p output input hdata
  have heq : start = start' := Option.some.inj (hstart.symm.trans hs')
  subst start'
  have hsim := Shared.ComplexityBridge.TM2Combined.core_run d.stackCount d.states d.symbols p
    d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol
    (Shared.ComplexityBridge.TM2FiniteReverse.finiteConfig d.stackCount d.states d.symbols p.length start) none [] [] n
  rw [hsteps] at hsim
  refine ⟨n,hn,c',?_,hout.1,t,ht,hfinish⟩
  rw [runSteps_add,hload]
  exact hsim

end Shared.ComplexityBridge.TM2BitstringFinish
