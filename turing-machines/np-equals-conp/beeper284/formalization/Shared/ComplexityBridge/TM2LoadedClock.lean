import Shared.ComplexityBridge.TM2PairPower

namespace Shared.ComplexityBridge.TM2LoadedClock
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2Combined Shared.ComplexityBridge.TM2FiniteReverse
open Shared.ComplexityBridge.TM2Loader Shared.ComplexityBridge.TM2BooleanInput

abbrev LStack := Shared.ComplexityBridge.TM2Loader.Stack
abbrev LLabel := Shared.ComplexityBridge.TM2Loader.Label
abbrev Key (ks : Nat) := Unit ⊕ (Bool ⊕ Fin (ks+1))
abbrev Label (p : Program) := LLabel ⊕ (Bool ⊕ Fin (p.length+1))
abbrev State (states : Nat) := Option Bool × Fin (states+1)
def Alphabet (ks symbols : Nat) : Key ks → Type
  | .inl _ => Bool
  | .inr (.inl _) => Bool
  | .inr (.inr _) => Fin (symbols+1)

def loaderKey (ks input : Nat) : LStack → Key ks
  | .input => .inr (.inl false)
  | .scratch => .inr (.inl true)
  | .output => .inr (.inr (clip ks input))

def loaderStacks (ks symbols input : Nat) (ticks : List Bool)
    (S : (s : LStack) → List (TM2Loader.Alphabet symbols s))
    (other : Fin (ks+1) → List (Fin (symbols+1))) : (s : Key ks) → List (Alphabet ks symbols s)
  | .inl _ => ticks
  | .inr (.inl false) => S .input
  | .inr (.inl true) => S .scratch
  | .inr (.inr j) => Function.update other (clip ks input) (S .output) j

theorem update_input (ks symbols input : Nat) (ticks : List Bool)
    (S : (s : LStack) → List (TM2Loader.Alphabet symbols s))
    (other : Fin (ks+1) → List (Fin (symbols+1))) (xs : List (Bool)) :
    loaderStacks ks symbols input ticks (Function.update S .input xs) other =
      Function.update (loaderStacks ks symbols input ticks S other) (loaderKey ks input .input) xs := by
  funext j
  cases j with
  | inl u => cases u; simp [loaderStacks,loaderKey,Function.update] <;> rfl
  | inr j =>
    cases j with
    | inl b => cases b <;> simp [loaderStacks,loaderKey,Function.update] <;> rfl
    | inr j =>
      by_cases h : j = clip ks input
      · subst j; simp [loaderStacks,loaderKey,Function.update] <;> rfl
      · simp [loaderStacks,loaderKey,Function.update,h] <;> rfl

theorem update_scratch (ks symbols input : Nat) (ticks : List Bool)
    (S : (s : LStack) → List (TM2Loader.Alphabet symbols s))
    (other : Fin (ks+1) → List (Fin (symbols+1))) (xs : List (Bool)) :
    loaderStacks ks symbols input ticks (Function.update S .scratch xs) other =
      Function.update (loaderStacks ks symbols input ticks S other) (loaderKey ks input .scratch) xs := by
  funext j
  cases j with
  | inl u => cases u; simp [loaderStacks,loaderKey,Function.update] <;> rfl
  | inr j =>
    cases j with
    | inl b => cases b <;> simp [loaderStacks,loaderKey,Function.update] <;> rfl
    | inr j =>
      by_cases h : j = clip ks input
      · subst j; simp [loaderStacks,loaderKey,Function.update] <;> rfl
      · simp [loaderStacks,loaderKey,Function.update,h] <;> rfl

theorem update_output (ks symbols input : Nat) (ticks : List Bool)
    (S : (s : LStack) → List (TM2Loader.Alphabet symbols s))
    (other : Fin (ks+1) → List (Fin (symbols+1))) (xs : List (Fin (symbols+1))) :
    loaderStacks ks symbols input ticks (Function.update S .output xs) other =
      Function.update (loaderStacks ks symbols input ticks S other) (loaderKey ks input .output) xs := by
  funext j
  cases j with
  | inl u => cases u; simp [loaderStacks,loaderKey,Function.update] <;> rfl
  | inr j =>
    cases j with
    | inl b => cases b <;> simp [loaderStacks,loaderKey,Function.update] <;> rfl
    | inr j =>
      by_cases h : j = clip ks input
      · subst j; simp [loaderStacks,loaderKey,Function.update] <;> rfl
      · simp [loaderStacks,loaderKey,Function.update,h] <;> rfl

def liftLoader (ks states symbols input : Nat) (p : Program) :
    Stmt (TM2Loader.Alphabet symbols) LLabel (Option Bool) →
      Stmt (Alphabet ks symbols) (Label p) (State states)
  | .push .input f q => .push (.inr (.inl false)) (fun v => f v.1) (liftLoader ks states symbols input p q)
  | .push .scratch f q => .push (.inr (.inl true)) (fun v => f v.1) (liftLoader ks states symbols input p q)
  | .push .output f q => .push (.inr (.inr (clip ks input))) (fun v => f v.1) (liftLoader ks states symbols input p q)
  | .peek .input f q => .peek (.inr (.inl false)) (fun v h => (f v.1 h,v.2)) (liftLoader ks states symbols input p q)
  | .peek .scratch f q => .peek (.inr (.inl true)) (fun v h => (f v.1 h,v.2)) (liftLoader ks states symbols input p q)
  | .peek .output f q => .peek (.inr (.inr (clip ks input))) (fun v h => (f v.1 h,v.2)) (liftLoader ks states symbols input p q)
  | .pop .input f q => .pop (.inr (.inl false)) (fun v h => (f v.1 h,v.2)) (liftLoader ks states symbols input p q)
  | .pop .scratch f q => .pop (.inr (.inl true)) (fun v h => (f v.1 h,v.2)) (liftLoader ks states symbols input p q)
  | .pop .output f q => .pop (.inr (.inr (clip ks input))) (fun v h => (f v.1 h,v.2)) (liftLoader ks states symbols input p q)
  | .load f q => .load (fun v => (f v.1,v.2)) (liftLoader ks states symbols input p q)
  | .branch f q r => .branch (fun v => f v.1) (liftLoader ks states symbols input p q) (liftLoader ks states symbols input p r)
  | .goto f => .goto (fun v => .inl (f v.1))
  | .halt => .halt

def loaderEmbed (ks states symbols input : Nat) (p : Program) (ticks : List Bool)
    (other : Fin (ks+1) → List (Fin (symbols+1))) (state : Fin (states+1))
    (c : (loader symbols 0 0).Cfg) : Cfg (Alphabet ks symbols) (Label p) (State states) :=
  ⟨c.l.map Sum.inl,(c.var,state),loaderStacks ks symbols input ticks c.stk other⟩

set_option backward.isDefEq.respectTransparency false in
theorem liftLoader_aux (ks states symbols input : Nat) (p : Program)
    (q : Stmt (TM2Loader.Alphabet symbols) LLabel (Option Bool)) (v : Option Bool)
    (ticks : List Bool) (other : Fin (ks+1) → List (Fin (symbols+1))) (state : Fin (states+1))
    (S : (s : LStack) → List (TM2Loader.Alphabet symbols s)) :
    stepAux (liftLoader ks states symbols input p q) (v,state) (loaderStacks ks symbols input ticks S other) =
      loaderEmbed ks states symbols input p ticks other state (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih (f v) S
  | push s f q ih =>
    cases s with
    | input =>
      simp only [liftLoader,stepAux,loaderStacks,Function.update_self]
      have hu := update_input ks symbols input ticks S other (f v::S .input)
      simp only [loaderKey] at hu
      rw [← hu]
      exact ih v _
    | scratch =>
      simp only [liftLoader,stepAux,loaderStacks,Function.update_self]
      have hu := update_scratch ks symbols input ticks S other (f v::S .scratch)
      simp only [loaderKey] at hu
      rw [← hu]
      exact ih v _
    | output =>
      simp only [liftLoader,stepAux,loaderStacks,Function.update_self]
      have hu := update_output ks symbols input ticks S other (f v::S .output)
      simp only [loaderKey] at hu
      rw [← hu]
      exact ih v _
  | peek s f q ih =>
    cases s with
    | input =>
      simp only [liftLoader,stepAux,loaderStacks,Function.update_self]
      exact ih (f v (S .input).head?) S
    | scratch =>
      simp only [liftLoader,stepAux,loaderStacks,Function.update_self]
      exact ih (f v (S .scratch).head?) S
    | output =>
      simp only [liftLoader,stepAux,loaderStacks,Function.update_self]
      exact ih (f v (S .output).head?) S
  | pop s f q ih =>
    cases s with
    | input =>
      simp only [liftLoader,stepAux,loaderStacks,Function.update_self]
      have hu := update_input ks symbols input ticks S other (S .input).tail
      simp only [loaderKey] at hu
      rw [← hu]
      exact ih (f v (S .input).head?) _
    | scratch =>
      simp only [liftLoader,stepAux,loaderStacks,Function.update_self]
      have hu := update_scratch ks symbols input ticks S other (S .scratch).tail
      simp only [loaderKey] at hu
      rw [← hu]
      exact ih (f v (S .scratch).head?) _
    | output =>
      simp only [liftLoader,stepAux,loaderStacks,Function.update_self]
      have hu := update_output ks symbols input ticks S other (S .output).tail
      simp only [loaderKey] at hu
      rw [← hu]
      exact ih (f v (S .output).head?) _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftLoader,stepAux,h,ihq,ihr]

def clockKey (ks : Nat) : Bool ⊕ Fin (ks+1) → Key ks
  | .inl false => .inl ()
  | .inl true => .inr (.inl true)
  | .inr j => .inr (.inr j)

def clockStacks (ks symbols : Nat) (input : List Bool)
    (S : (s : Bool ⊕ Fin (ks+1)) → List (TM2Combined.Alphabet ks symbols s)) :
    (s : Key ks) → List (Alphabet ks symbols s)
  | .inl _ => S (.inl false)
  | .inr (.inl false) => input
  | .inr (.inl true) => S (.inl true)
  | .inr (.inr j) => S (.inr j)

theorem clock_update_false (ks symbols : Nat) (input : List Bool)
    (S : (s : Bool ⊕ Fin (ks+1)) → List (TM2Combined.Alphabet ks symbols s)) (xs : List (Bool)) :
    clockStacks ks symbols input (Function.update S (.inl false) xs) =
      Function.update (clockStacks ks symbols input S) (clockKey ks (.inl false)) xs := by
  funext s
  cases s with
  | inl u => cases u; simp [clockStacks,clockKey,Function.update] <;> rfl
  | inr s =>
    cases s with
    | inl b => cases b <;> simp [clockStacks,clockKey,Function.update] <;> rfl
    | inr a => simp [clockStacks,clockKey,Function.update] <;> rfl

theorem clock_update_true (ks symbols : Nat) (input : List Bool)
    (S : (s : Bool ⊕ Fin (ks+1)) → List (TM2Combined.Alphabet ks symbols s)) (xs : List (Bool)) :
    clockStacks ks symbols input (Function.update S (.inl true) xs) =
      Function.update (clockStacks ks symbols input S) (clockKey ks (.inl true)) xs := by
  funext s
  cases s with
  | inl u => cases u; simp [clockStacks,clockKey,Function.update] <;> rfl
  | inr s =>
    cases s with
    | inl b => cases b <;> simp [clockStacks,clockKey,Function.update] <;> rfl
    | inr a => simp [clockStacks,clockKey,Function.update] <;> rfl

theorem clock_update_core (ks symbols : Nat) (input : List Bool)
    (S : (s : Bool ⊕ Fin (ks+1)) → List (TM2Combined.Alphabet ks symbols s)) (j : Fin (ks+1)) (xs : List (Fin (symbols+1))) :
    clockStacks ks symbols input (Function.update S (.inr j) xs) =
      Function.update (clockStacks ks symbols input S) (clockKey ks (.inr j)) xs := by
  funext s
  cases s with
  | inl u => cases u; simp [clockStacks,clockKey,Function.update] <;> rfl
  | inr s =>
    cases s with
    | inl b => cases b <;> simp [clockStacks,clockKey,Function.update] <;> rfl
    | inr a =>
      by_cases h : a = j
      · subst a; simp [clockStacks,clockKey,Function.update] <;> rfl
      · simp [clockStacks,clockKey,Function.update,h] <;> rfl

def liftClock (ks states symbols : Nat) (p : Program) :
    Stmt (TM2Combined.Alphabet ks symbols) (Bool ⊕ Fin (p.length+1)) (State states) →
      Stmt (Alphabet ks symbols) (Label p) (State states)
  | .push (.inl false) f q => .push (.inl ()) f (liftClock ks states symbols p q)
  | .push (.inl true) f q => .push (.inr (.inl true)) f (liftClock ks states symbols p q)
  | .push (.inr j) f q => .push (.inr (.inr j)) f (liftClock ks states symbols p q)
  | .peek (.inl false) f q => .peek (.inl ()) f (liftClock ks states symbols p q)
  | .peek (.inl true) f q => .peek (.inr (.inl true)) f (liftClock ks states symbols p q)
  | .peek (.inr j) f q => .peek (.inr (.inr j)) f (liftClock ks states symbols p q)
  | .pop (.inl false) f q => .pop (.inl ()) f (liftClock ks states symbols p q)
  | .pop (.inl true) f q => .pop (.inr (.inl true)) f (liftClock ks states symbols p q)
  | .pop (.inr j) f q => .pop (.inr (.inr j)) f (liftClock ks states symbols p q)
  | .load f q => .load f (liftClock ks states symbols p q)
  | .branch f q r => .branch f (liftClock ks states symbols p q) (liftClock ks states symbols p r)
  | .goto f => .goto (fun v => .inr (f v))
  | .halt => .halt

def clockEmbed (ks states symbols : Nat) (p : Program) (input : List Bool)
    (c : (Shared.ComplexityBridge.TM2UnaryClock.clocked ks states symbols p 0 0 0 0).Cfg) :
    Cfg (Alphabet ks symbols) (Label p) (State states) :=
  ⟨c.l.map Sum.inr,c.var,clockStacks ks symbols input c.stk⟩

set_option backward.isDefEq.respectTransparency false in
theorem liftClock_aux (ks states symbols : Nat) (p : Program)
    (q : Stmt (TM2Combined.Alphabet ks symbols) (Bool ⊕ Fin (p.length+1)) (State states))
    (v : State states) (input : List Bool)
    (S : (s : Bool ⊕ Fin (ks+1)) → List (TM2Combined.Alphabet ks symbols s)) :
    stepAux (liftClock ks states symbols p q) v (clockStacks ks symbols input S) =
      clockEmbed ks states symbols p input (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih (f v) S
  | push s f q ih =>
    cases s with
    | inl b =>
      cases b with
      | false =>
        simp only [liftClock,stepAux,clockStacks]
        have hu := clock_update_false ks symbols input S (f v::S (.inl false))
        simp only [clockKey] at hu
        rw [← hu]
        exact ih v _
      | true =>
        simp only [liftClock,stepAux,clockStacks]
        have hu := clock_update_true ks symbols input S (f v::S (.inl true))
        simp only [clockKey] at hu
        rw [← hu]
        exact ih v _
    | inr j =>
      simp only [liftClock,stepAux,clockStacks]
      have hu := clock_update_core ks symbols input S j (f v::S (.inr j))
      simp only [clockKey] at hu
      rw [← hu]
      exact ih v _
  | peek s f q ih =>
    cases s with
    | inl b =>
      cases b with
      | false =>
        simp only [liftClock,stepAux,clockStacks]
        exact ih (f v (S (.inl false)).head?) S
      | true =>
        simp only [liftClock,stepAux,clockStacks]
        exact ih (f v (S (.inl true)).head?) S
    | inr j =>
      simp only [liftClock,stepAux,clockStacks]
      exact ih (f v (S (.inr j)).head?) S
  | pop s f q ih =>
    cases s with
    | inl b =>
      cases b with
      | false =>
        simp only [liftClock,stepAux,clockStacks]
        have hu := clock_update_false ks symbols input S (S (.inl false)).tail
        simp only [clockKey] at hu
        rw [← hu]
        exact ih (f v (S (.inl false)).head?) _
      | true =>
        simp only [liftClock,stepAux,clockStacks]
        have hu := clock_update_true ks symbols input S (S (.inl true)).tail
        simp only [clockKey] at hu
        rw [← hu]
        exact ih (f v (S (.inl true)).head?) _
    | inr j =>
      simp only [liftClock,stepAux,clockStacks]
      have hu := clock_update_core ks symbols input S j (S (.inr j)).tail
      simp only [clockKey] at hu
      rw [← hu]
      exact ih (f v (S (.inr j)).head?) _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftClock,stepAux,h,ihq,ihr]

def program (ks states symbols : Nat) (p : Program) (input main z o : Nat) :
    Label p → Stmt (Alphabet ks symbols) (Label p) (State states)
  | .inl .done => .goto (fun _ => .inr (.inr (clip p.length main)))
  | .inl l => liftLoader ks states symbols input p (TM2Loader.program symbols z o l)
  | .inr l => liftClock ks states symbols p (TM2UnaryClock.program ks states symbols p l)

def machine (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat) : Turing.FinTM2 where
  K := Key ks
  k₀ := .inr (.inl false)
  k₁ := .inr (.inr (clip ks output))
  Γ := Alphabet ks symbols
  Λ := Label p
  main := .inl .scan
  σ := State states
  initialState := (none,clip states initial)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program ks states symbols p input main z o

def loaderTerminal (symbols : Nat) (c : (loader symbols 0 0).Cfg) : Prop := c.l = some .done
noncomputable instance (symbols : Nat) : DecidablePred (loaderTerminal symbols) := fun _ => Classical.propDecidable _

theorem loader_stable (symbols z o : Nat) (c : (loader symbols z o).Cfg) (h : loaderTerminal symbols c) :
    (loader symbols z o).step c = some c := by
  cases c with
  | mk l v S =>
    change l = some TM2Loader.Label.done at h
    subst l
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem loader_step (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat)
    (ticks : List Bool) (other : Fin (ks+1) → List (Fin (symbols+1))) (state : Fin (states+1))
    (c : (loader symbols z o).Cfg) (h : ¬ loaderTerminal symbols c) :
    (machine ks states symbols p input output main initial z o).step
      (loaderEmbed ks states symbols input p ticks other state c) =
        ((loader symbols z o).step c).map (loaderEmbed ks states symbols input p ticks other state) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      cases l with
      | done => exact False.elim (h rfl)
      | scan | restore =>
        change some (stepAux (liftLoader ks states symbols input p (TM2Loader.program symbols z o _))
          (v,state) (loaderStacks ks symbols input ticks S other)) = _
        rw [liftLoader_aux]
        rfl

set_option backward.isDefEq.respectTransparency false in
theorem clock_step (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat)
    (bits : List Bool) (c : (TM2UnaryClock.clocked ks states symbols p input output main initial).Cfg) :
    (machine ks states symbols p input output main initial z o).step (clockEmbed ks states symbols p bits c) =
      ((TM2UnaryClock.clocked ks states symbols p input output main initial).step c).map
        (clockEmbed ks states symbols p bits) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      change some (stepAux (liftClock ks states symbols p (TM2UnaryClock.program ks states symbols p l))
        v (clockStacks ks symbols bits S)) = _
      rw [liftClock_aux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem clock_run (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat)
    (bits : List Bool) (c : (TM2UnaryClock.clocked ks states symbols p input output main initial).Cfg) (n : Nat) :
    runSteps (machine ks states symbols p input output main initial z o).step n (clockEmbed ks states symbols p bits c) =
      (runSteps (TM2UnaryClock.clocked ks states symbols p input output main initial).step n c).map
        (clockEmbed ks states symbols p bits) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [runSteps_front, runSteps_front, clock_step]
    cases h : (TM2UnaryClock.clocked ks states symbols p input output main initial).step c with
    | none => rfl
    | some c' => exact ih c'

/-- The exact loader-to-clock handoff retains the unary ticks and moves the
encoded Boolean input into the finite core's input alphabet. -/
theorem dispatch (ks states symbols : Nat) (p : Program) (input output main initial z o : Nat)
    (ticks : List Bool) (os : List (Fin (symbols+1))) :
    (machine ks states symbols p input output main initial z o).step
      (loaderEmbed ks states symbols input p ticks (fun _ => []) (clip states initial)
        (TM2Loader.config symbols .done none [] [] os)) =
      some (clockEmbed ks states symbols p []
        (TM2UnaryClock.embed ks states symbols p.length none ticks
          (coreInit ks states symbols p input output main initial os (fun _ => [])))) := by
  change some (Cfg.mk (some (Sum.inr (Sum.inr (clip p.length main)))) (none,clip states initial)
    (loaderStacks ks symbols input ticks (TM2Loader.stackVals symbols [] [] os) (fun _ => [])) :
      (machine ks states symbols p input output main initial z o).Cfg) = _
  rfl

def preloaded (ks states symbols : Nat) (p : Program) (input initial z o : Nat)
    (ticks bits : List Bool) : (machine ks states symbols p input 0 0 initial z o).Cfg :=
  loaderEmbed ks states symbols input p ticks (fun _ => []) (clip states initial)
    (Turing.initList (loader symbols z o) bits)

set_option backward.isDefEq.respectTransparency false in
/-- Given a unary clock stack, the real input loader completes and dispatches
in at most its exact standalone cost plus one block, preserving all ticks. -/
theorem load_to_clock (d : InputData) (p : Program) (output : Nat) (ticks bits : List Bool)
    (hdata : validInputData d = true) :
    ∃ start, buildStart d bits = some start ∧
      ∃ n ≤ 2*bits.length+3,
        runSteps (machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
          d.falseSymbol d.trueSymbol).step n
          (loaderEmbed d.stackCount d.states d.symbols d.inputStack p ticks (fun _ => []) (clip d.states d.initialState)
            (Turing.initList (loader d.symbols d.falseSymbol d.trueSymbol) bits)) =
        some (clockEmbed d.stackCount d.states d.symbols p []
          (TM2UnaryClock.embed d.stackCount d.states d.symbols p.length none ticks
            (finiteConfig d.stackCount d.states d.symbols p.length start))) := by
  letI : DecidablePred (loaderTerminal d.symbols) := fun _ => Classical.propDecidable _
  obtain ⟨start, hs, hcore⟩ := coreInit_matches_numeric d p output bits hdata
  have hloader := TM2Loader.load_correct d.symbols d.falseSymbol d.trueSymbol bits
  obtain ⟨m, hm, hr⟩ := TM2UnaryTransfer.run_to_stable_lift
    (loader d.symbols d.falseSymbol d.trueSymbol).step
    (machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol).step
    (loaderEmbed d.stackCount d.states d.symbols d.inputStack p ticks (fun _ => []) (clip d.states d.initialState))
    (loaderTerminal d.symbols) (loader_stable d.symbols d.falseSymbol d.trueSymbol)
    (loader_step d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
      d.falseSymbol d.trueSymbol ticks (fun _ => []) (clip d.states d.initialState))
    (2*bits.length+2) (Turing.initList (loader d.symbols d.falseSymbol d.trueSymbol) bits)
    (TM2Loader.config d.symbols .done none [] [] (bits.map (TM2Loader.enc d.symbols d.falseSymbol d.trueSymbol)))
    (by rfl) hloader
  refine ⟨start, hs, m+1, by omega, ?_⟩
  rw [runSteps_add,hr]
  change (machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol).step (loaderEmbed d.stackCount d.states d.symbols d.inputStack p ticks
      (fun _ => []) (clip d.states d.initialState)
      (TM2Loader.config d.symbols .done none [] [] (bits.map (TM2Loader.enc d.symbols d.falseSymbol d.trueSymbol)))) = _
  rw [dispatch, hcore]

set_option backward.isDefEq.respectTransparency false in
/-- A checked timeout after `fuel` core blocks is reached after the real input
loader and at most one additional clock-expiration block. -/
theorem loaded_numeric_timeout (d : InputData) (p : Program) (output fuel : Nat) (bits : List Bool)
    (hdata : validInputData d = true) (hp : Shared.Codes.TM2Program.programValid p d.stackCount d.states d.symbols = true)
    (start result : Shared.Codes.TM2StatementExecution.Result)
    (hstart : buildStart d bits = some start)
    (hvalid : Shared.Codes.TM2StatementValidation.resultValid d.stackCount d.states d.symbols p.length start)
    (hrun : run p fuel start = .timeout result) :
    ∃ n ≤ 2*bits.length+fuel+4, ∃ c',
      CfgRel d.stackCount d.states d.symbols p.length c' (Shared.Codes.TM2StatementExecution.erase result) ∧
      runSteps (machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
        d.falseSymbol d.trueSymbol).step n
        (loaderEmbed d.stackCount d.states d.symbols d.inputStack p (List.replicate fuel true) (fun _ => [])
          (clip d.states d.initialState) (Turing.initList (loader d.symbols d.falseSymbol d.trueSymbol) bits)) =
        some (clockEmbed d.stackCount d.states d.symbols p []
          (TM2UnaryClock.timeoutCfg d.stackCount d.states d.symbols p.length c')) := by
  obtain ⟨start', hs, m, hm, hload⟩ := load_to_clock d p output (List.replicate fuel true) bits hdata
  have heq : start' = start := Option.some.inj (hs.symm.trans hstart)
  subst start'
  obtain ⟨c', hc, ht⟩ := TM2UnaryClock.numeric_timeout d.stackCount d.states d.symbols p d.inputStack output
    d.main d.initialState fuel hp start result hvalid hrun
  have ht' := clock_run d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol []
    (TM2UnaryClock.embed d.stackCount d.states d.symbols p.length none (List.replicate fuel true)
      (finiteConfig d.stackCount d.states d.symbols p.length start)) (fuel+1)
  rw [ht] at ht'
  refine ⟨m+(fuel+1), by omega, c', hc, ?_⟩
  rw [runSteps_add,hload]
  exact ht'

set_option backward.isDefEq.respectTransparency false in
/-- A checked halt within the clock is reached by the same composed loader and
clock machine, with its unused ticks and numeric result preserved. -/
theorem loaded_numeric_halt (d : InputData) (p : Program) (output fuel : Nat) (bits : List Bool)
    (hdata : validInputData d = true) (hp : Shared.Codes.TM2Program.programValid p d.stackCount d.states d.symbols = true)
    (start result : Shared.Codes.TM2StatementExecution.Result)
    (hstart : buildStart d bits = some start)
    (hvalid : Shared.Codes.TM2StatementValidation.resultValid d.stackCount d.states d.symbols p.length start)
    (hrun : run p fuel start = .halted result) :
    ∃ n ≤ 2*bits.length+fuel+3, ∃ m ≤ fuel, ∃ c' flag,
      CfgRel d.stackCount d.states d.symbols p.length c' (Shared.Codes.TM2StatementExecution.erase result) ∧ c'.l = none ∧
      runSteps (machine d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
        d.falseSymbol d.trueSymbol).step n
        (loaderEmbed d.stackCount d.states d.symbols d.inputStack p (List.replicate fuel true) (fun _ => [])
          (clip d.states d.initialState) (Turing.initList (loader d.symbols d.falseSymbol d.trueSymbol) bits)) =
        some (clockEmbed d.stackCount d.states d.symbols p []
          (TM2UnaryClock.embed d.stackCount d.states d.symbols p.length flag ((List.replicate fuel true).drop m) c')) := by
  obtain ⟨start', hs, a, ha, hload⟩ := load_to_clock d p output (List.replicate fuel true) bits hdata
  have heq : start' = start := Option.some.inj (hs.symm.trans hstart)
  subst start'
  obtain ⟨m, hm, c', flag, hc, hh, ht⟩ := TM2UnaryClock.numeric_halt d.stackCount d.states d.symbols p d.inputStack output
    d.main d.initialState fuel hp start result hvalid hrun
  have ht' := clock_run d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol []
    (TM2UnaryClock.embed d.stackCount d.states d.symbols p.length none (List.replicate fuel true)
      (finiteConfig d.stackCount d.states d.symbols p.length start)) m
  rw [ht] at ht'
  refine ⟨a+m, by omega, m, hm, c', flag, hc, hh, ?_⟩
  rw [runSteps_add,hload]
  exact ht'

end Shared.ComplexityBridge.TM2LoadedClock
