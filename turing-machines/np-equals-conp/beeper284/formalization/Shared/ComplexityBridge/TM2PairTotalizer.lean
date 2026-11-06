import Shared.ComplexityBridge.TM2ClockFlag
import Shared.ComplexityBridge.TM2VerifierValidity

namespace Shared.ComplexityBridge.TM2PairTotalizer
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2PairClock Shared.ComplexityBridge.TM2FiniteReverse
abbrev Source := Shared.ComplexityBridge.TM2PairClock.machine
abbrev Key (ks : Nat) := Shared.ComplexityBridge.TM2PairClock.Key ks
abbrev Alphabet (ks symbols : Nat) := Shared.ComplexityBridge.TM2PairClock.Alphabet ks symbols
abbrev SourceLabel (k : Nat) (p : Program) := Shared.ComplexityBridge.TM2PairClock.Label k p
abbrev SourceState (states : Nat) := Shared.ComplexityBridge.TM2PairClock.State states
abbrev CleanState (states : Nat) := Shared.ComplexityBridge.TM2AuxSweep.AuxState states
abbrev CleanLabel (ks : Nat) := Shared.ComplexityBridge.TM2AuxSweep.Phase ⊕ Shared.ComplexityBridge.TM2StrictCleanup.Label ks
abbrev Label (ks k : Nat) (p : Program) := SourceLabel k p ⊕ CleanLabel ks
abbrev State (states : Nat) := SourceState states ⊕ CleanState states

def runState : State states → SourceState states
  | .inl s => s
  | .inr _ => .inl (none,false)
def cleanState (states initial : Nat) : State states → CleanState states
  | .inl _ => (false,clip states initial,false)
  | .inr s => s

def successful : SourceState states → Bool
  | .inl _ => false
  | .inr (flag,_) => flag.isSome

def coreState (states initial : Nat) : SourceState states → Fin (states+1)
  | .inl _ => clip states initial
  | .inr (_,v) => v

def beginAux {ks k : Nat} {p : Program} : Label ks k p := .inr (.inl ⟨0,by decide⟩)
def auxLabel {ks k : Nat} {p : Program} (l : Shared.ComplexityBridge.TM2AuxSweep.Phase) : Label ks k p := .inr (.inl l)
def strictLabel {ks k : Nat} {p : Program} (l : Shared.ComplexityBridge.TM2StrictCleanup.Label ks) : Label ks k p := .inr (.inr l)

def runEmbed (ks states symbols initial k : Nat) (p : Program)
    (c : (Source ks states symbols k p 0 0 0 0 0 0).Cfg) : Cfg (Alphabet ks symbols) (Label ks k p) (State states) :=
  match c.l with
  | some l => ⟨some (.inl l),.inl c.var,c.stk⟩
  | none => ⟨some beginAux,.inr (successful c.var,coreState states initial c.var,false),c.stk⟩

def liftRun (ks states symbols initial k : Nat) (p : Program) :
    Stmt (Alphabet ks symbols) (SourceLabel k p) (SourceState states) →
      Stmt (Alphabet ks symbols) (Label ks k p) (State states)
  | .push i f q => .push i (fun s => f (runState s)) (liftRun ks states symbols initial k p q)
  | .peek i f q => .peek i (fun s h => .inl (f (runState s) h)) (liftRun ks states symbols initial k p q)
  | .pop i f q => .pop i (fun s h => .inl (f (runState s) h)) (liftRun ks states symbols initial k p q)
  | .load f q => .load (fun s => .inl (f (runState s))) (liftRun ks states symbols initial k p q)
  | .branch f q r => .branch (fun s => f (runState s)) (liftRun ks states symbols initial k p q) (liftRun ks states symbols initial k p r)
  | .goto f => .goto (fun s => .inl (f (runState s)))
  | .halt => .load (fun s => .inr (successful (runState s),coreState states initial (runState s),false))
      (.goto (fun _ => beginAux))

theorem liftRun_aux (ks states symbols initial k : Nat) (p : Program)
    (q : Stmt (Alphabet ks symbols) (SourceLabel k p) (SourceState states))
    (v : SourceState states) (S : (j : Key ks) → List (Alphabet ks symbols j)) :
    stepAux (liftRun ks states symbols initial k p q) (.inl v) S =
      runEmbed ks states symbols initial k p (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih (f v) S
  | push i f q ih => exact ih v _
  | peek i f q ih => exact ih _ S
  | pop i f q ih => exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftRun,stepAux,runState,h,ihq,ihr]

def auxEmbed (ks states symbols k : Nat) (p : Program)
    (c : (Shared.ComplexityBridge.TM2AuxSweep.machine ks states symbols 0).Cfg) :
    Cfg (Alphabet ks symbols) (Label ks k p) (State states) :=
  ⟨c.l.map auxLabel,.inr c.var,c.stk⟩

def liftAux (ks states symbols initial k : Nat) (p : Program) :
    Stmt (Alphabet ks symbols) Shared.ComplexityBridge.TM2AuxSweep.Phase (CleanState states) →
      Stmt (Alphabet ks symbols) (Label ks k p) (State states)
  | .push i f q => .push i (fun s => f (cleanState states initial s)) (liftAux ks states symbols initial k p q)
  | .peek i f q => .peek i (fun s h => .inr (f (cleanState states initial s) h)) (liftAux ks states symbols initial k p q)
  | .pop i f q => .pop i (fun s h => .inr (f (cleanState states initial s) h)) (liftAux ks states symbols initial k p q)
  | .load f q => .load (fun s => .inr (f (cleanState states initial s))) (liftAux ks states symbols initial k p q)
  | .branch f q r => .branch (fun s => f (cleanState states initial s)) (liftAux ks states symbols initial k p q) (liftAux ks states symbols initial k p r)
  | .goto f => .goto (fun s => auxLabel (f (cleanState states initial s)))
  | .halt => .halt

theorem liftAux_aux (ks states symbols initial k : Nat) (p : Program)
    (q : Stmt (Alphabet ks symbols) Shared.ComplexityBridge.TM2AuxSweep.Phase (CleanState states))
    (v : CleanState states) (S : (j : Key ks) → List (Alphabet ks symbols j)) :
    stepAux (liftAux ks states symbols initial k p q) (.inr v) S =
      auxEmbed ks states symbols k p (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih (f v) S
  | push i f q ih => exact ih v _
  | peek i f q ih => exact ih _ S
  | pop i f q ih => exact ih _ _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftAux,stepAux,cleanState,h,ihq,ihr]

def strictKey (ks : Nat) : Bool ⊕ Fin (ks+1) → Key ks
  | .inl b => .inl (.inl b)
  | .inr j => .inr j

def strictStacks (ks symbols : Nat)
    (S : (s : Bool ⊕ Fin (ks+1)) → List (Shared.ComplexityBridge.TM2Combined.Alphabet ks symbols s)) :
    (s : Key ks) → List (Alphabet ks symbols s)
  | .inl (.inl b) => S (.inl b)
  | .inl (.inr _) => []
  | .inr j => S (.inr j)

theorem strict_update_false (ks symbols : Nat)
    (S : (s : Bool ⊕ Fin (ks+1)) → List (Shared.ComplexityBridge.TM2Combined.Alphabet ks symbols s))
    (xs : List (Bool)) :
    strictStacks ks symbols (Function.update S (.inl false) xs) =
      Function.update (strictStacks ks symbols S) (strictKey ks (.inl false)) xs := by
  funext s
  cases s with
  | inl a =>
    cases a with
    | inl b => cases b <;> simp [strictStacks,strictKey,Function.update] <;> rfl
    | inr q => cases q <;> simp [strictStacks,strictKey,Function.update] <;> rfl
  | inr a => simp [strictStacks,strictKey,Function.update] <;> rfl

theorem strict_update_true (ks symbols : Nat)
    (S : (s : Bool ⊕ Fin (ks+1)) → List (Shared.ComplexityBridge.TM2Combined.Alphabet ks symbols s))
    (xs : List (Bool)) :
    strictStacks ks symbols (Function.update S (.inl true) xs) =
      Function.update (strictStacks ks symbols S) (strictKey ks (.inl true)) xs := by
  funext s
  cases s with
  | inl a =>
    cases a with
    | inl b => cases b <;> simp [strictStacks,strictKey,Function.update] <;> rfl
    | inr q => cases q <;> simp [strictStacks,strictKey,Function.update] <;> rfl
  | inr a => simp [strictStacks,strictKey,Function.update] <;> rfl

theorem strict_update_core (ks symbols : Nat)
    (S : (s : Bool ⊕ Fin (ks+1)) → List (Shared.ComplexityBridge.TM2Combined.Alphabet ks symbols s))
    (j : Fin (ks+1)) (xs : List (Fin (symbols+1))) :
    strictStacks ks symbols (Function.update S (.inr j) xs) =
      Function.update (strictStacks ks symbols S) (strictKey ks (.inr j)) xs := by
  funext s
  cases s with
  | inl a =>
    cases a with
    | inl b => cases b <;> simp [strictStacks,strictKey,Function.update] <;> rfl
    | inr q => cases q <;> simp [strictStacks,strictKey,Function.update] <;> rfl
  | inr a =>
    by_cases h : a = j
    · subst a; simp [strictStacks,strictKey,Function.update] <;> rfl
    · simp [strictStacks,strictKey,Function.update,h] <;> rfl

def strictEmbed (ks states symbols k : Nat) (p : Program)
    (c : (Shared.ComplexityBridge.TM2StrictCleanup.machine ks states symbols 0 0 0 0).Cfg) :
    Cfg (Alphabet ks symbols) (Label ks k p) (State states) :=
  match c.l with
  | none => ⟨none,.inl (.inl (none,false)),strictStacks ks symbols c.stk⟩
  | some l => ⟨some (strictLabel l),.inr c.var,strictStacks ks symbols c.stk⟩

def liftStrict (ks states symbols initial k : Nat) (p : Program) :
    Stmt (Shared.ComplexityBridge.TM2Combined.Alphabet ks symbols)
      (Shared.ComplexityBridge.TM2StrictCleanup.Label ks) (CleanState states) →
      Stmt (Alphabet ks symbols) (Label ks k p) (State states)
  | .push (.inl false) f q => .push (.inl (.inl false)) (fun s => f (cleanState states initial s)) (liftStrict ks states symbols initial k p q)
  | .push (.inl true) f q => .push (.inl (.inl true)) (fun s => f (cleanState states initial s)) (liftStrict ks states symbols initial k p q)
  | .push (.inr j) f q => .push (.inr j) (fun s => f (cleanState states initial s)) (liftStrict ks states symbols initial k p q)
  | .peek (.inl false) f q => .peek (.inl (.inl false)) (fun s h => .inr (f (cleanState states initial s) h)) (liftStrict ks states symbols initial k p q)
  | .peek (.inl true) f q => .peek (.inl (.inl true)) (fun s h => .inr (f (cleanState states initial s) h)) (liftStrict ks states symbols initial k p q)
  | .peek (.inr j) f q => .peek (.inr j) (fun s h => .inr (f (cleanState states initial s) h)) (liftStrict ks states symbols initial k p q)
  | .pop (.inl false) f q => .pop (.inl (.inl false)) (fun s h => .inr (f (cleanState states initial s) h)) (liftStrict ks states symbols initial k p q)
  | .pop (.inl true) f q => .pop (.inl (.inl true)) (fun s h => .inr (f (cleanState states initial s) h)) (liftStrict ks states symbols initial k p q)
  | .pop (.inr j) f q => .pop (.inr j) (fun s h => .inr (f (cleanState states initial s) h)) (liftStrict ks states symbols initial k p q)
  | .load f q => .load (fun s => .inr (f (cleanState states initial s))) (liftStrict ks states symbols initial k p q)
  | .branch f q r => .branch (fun s => f (cleanState states initial s))
      (liftStrict ks states symbols initial k p q) (liftStrict ks states symbols initial k p r)
  | .goto f => .goto (fun s => strictLabel (f (cleanState states initial s)))
  | .halt => .load (fun _ => .inl (.inl (none,false))) .halt

set_option backward.isDefEq.respectTransparency false in
theorem liftStrict_aux (ks states symbols initial k : Nat) (p : Program)
    (q : Stmt (Shared.ComplexityBridge.TM2Combined.Alphabet ks symbols)
      (Shared.ComplexityBridge.TM2StrictCleanup.Label ks) (CleanState states))
    (v : CleanState states) (S : (s : Bool ⊕ Fin (ks+1)) → List (Shared.ComplexityBridge.TM2Combined.Alphabet ks symbols s)) :
    stepAux (liftStrict ks states symbols initial k p q) (.inr v) (strictStacks ks symbols S) =
      strictEmbed ks states symbols k p (stepAux q v S) := by
  induction q generalizing v S with
  | halt => rfl
  | goto f => rfl
  | load f q ih => exact ih (f v) S
  | push s f q ih =>
    cases s with
    | inl b =>
      cases b with
      | false =>
        simp only [liftStrict,stepAux,cleanState,strictStacks]
        have hu := strict_update_false ks symbols S (f v::S (.inl false))
        simp only [strictKey] at hu
        rw [← hu]
        exact ih v _
      | true =>
        simp only [liftStrict,stepAux,cleanState,strictStacks]
        have hu := strict_update_true ks symbols S (f v::S (.inl true))
        simp only [strictKey] at hu
        rw [← hu]
        exact ih v _
    | inr j =>
      simp only [liftStrict,stepAux,cleanState,strictStacks]
      have hu := strict_update_core ks symbols S j (f v::S (.inr j))
      simp only [strictKey] at hu
      rw [← hu]
      exact ih v _
  | peek s f q ih =>
    cases s with
    | inl b =>
      cases b with
      | false =>
        simp only [liftStrict,stepAux,cleanState,strictStacks]
        exact ih (f v (S (.inl false)).head?) S
      | true =>
        simp only [liftStrict,stepAux,cleanState,strictStacks]
        exact ih (f v (S (.inl true)).head?) S
    | inr j =>
      simp only [liftStrict,stepAux,cleanState,strictStacks]
      exact ih (f v (S (.inr j)).head?) S
  | pop s f q ih =>
    cases s with
    | inl b =>
      cases b with
      | false =>
        simp only [liftStrict,stepAux,cleanState,strictStacks]
        have hu := strict_update_false ks symbols S (S (.inl false)).tail
        simp only [strictKey] at hu
        rw [← hu]
        exact ih (f v (S (.inl false)).head?) _
      | true =>
        simp only [liftStrict,stepAux,cleanState,strictStacks]
        have hu := strict_update_true ks symbols S (S (.inl true)).tail
        simp only [strictKey] at hu
        rw [← hu]
        exact ih (f v (S (.inl true)).head?) _
    | inr j =>
      simp only [liftStrict,stepAux,cleanState,strictStacks]
      have hu := strict_update_core ks symbols S j (S (.inr j)).tail
      simp only [strictKey] at hu
      rw [← hu]
      exact ih (f v (S (.inr j)).head?) _
  | branch f q r ihq ihr => by_cases h : f v <;> simp [liftStrict,stepAux,cleanState,h,ihq,ihr]

def program (ks states symbols initial k : Nat) (p : Program) (input main inZero inOne output z one : Nat) :
    Label ks k p → Stmt (Alphabet ks symbols) (Label ks k p) (State states)
  | .inl l => liftRun ks states symbols initial k p
      (Shared.ComplexityBridge.TM2PairClock.program ks states symbols initial k p input main inZero inOne l)
  | .inr (.inl l) => if l = Shared.ComplexityBridge.TM2AuxSweep.done then
      .branch (fun s => (cleanState states initial s).1)
        (.load (fun s => .inr (false,(cleanState states initial s).2.1,false))
          (.goto (fun _ => strictLabel (.inl false))))
        (.load (fun s => .inr (false,(cleanState states initial s).2.1,false))
          (.goto (fun _ => strictLabel (.inr ⟨0,by omega⟩))))
    else liftAux ks states symbols initial k p (Shared.ComplexityBridge.TM2AuxSweep.program ks states symbols l)
  | .inr (.inr l) => liftStrict ks states symbols initial k p
      (Shared.ComplexityBridge.TM2StrictCleanup.program ks states symbols initial output z one l)

def machine (ks states symbols : Nat) (k : Nat) (p : Program)
    (input output main initial inZero inOne z one : Nat) : Turing.FinTM2 where
  K := Key ks
  k₀ := .inl (.inl false)
  k₁ := .inl (.inl true)
  Γ := Alphabet ks symbols
  Λ := Label ks k p
  main := .inl (.inl (.inl .start))
  σ := State states
  initialState := .inl (.inl (none,false))
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := program ks states symbols initial k p input main inZero inOne output z one

set_option backward.isDefEq.respectTransparency false in
theorem run_step (ks states symbols : Nat) (k : Nat) (p : Program)
    (input output main initial inZero inOne z one : Nat)
    (c : (Source ks states symbols k p input output main initial inZero inOne).Cfg) (hactive : c.l ≠ none) :
    (machine ks states symbols k p input output main initial inZero inOne z one).step
      (runEmbed ks states symbols initial k p c) =
      ((Source ks states symbols k p input output main initial inZero inOne).step c).map
        (runEmbed ks states symbols initial k p) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => contradiction
    | some l =>
      change some (stepAux (liftRun ks states symbols initial k p
        (Shared.ComplexityBridge.TM2PairClock.program ks states symbols initial k p input main inZero inOne l)) (.inl v) S) = _
      rw [liftRun_aux]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every finite source run is mirrored, with the source halt redirected into
auxiliary-stack cleanup in the same transition. -/
theorem run_run (ks states symbols : Nat) (k : Nat) (p : Program)
    (input output main initial inZero inOne z one : Nat)
    (n : Nat) (c d : (Source ks states symbols k p input output main initial inZero inOne).Cfg)
    (h : runSteps (Source ks states symbols k p input output main initial inZero inOne).step n c = some d) :
    runSteps (machine ks states symbols k p input output main initial inZero inOne z one).step n
      (runEmbed ks states symbols initial k p c) = some (runEmbed ks states symbols initial k p d) := by
  induction n generalizing c with
  | zero =>
    change some c = some d at h
    cases h
    rfl
  | succ n ih =>
    rw [runSteps_front] at h
    change ((Source ks states symbols k p input output main initial inZero inOne).step c).bind
      (runSteps (Source ks states symbols k p input output main initial inZero inOne).step n) = some d at h
    cases hs : (Source ks states symbols k p input output main initial inZero inOne).step c with
    | none => rw [hs] at h; contradiction
    | some c' =>
      have hactive : c.l ≠ none := by
        intro hl
        have hn : (Source ks states symbols k p input output main initial inZero inOne).step c = none := by
          cases c with
          | mk l v S => cases l with
            | none => rfl
            | some l => simp at hl
        rw [hn] at hs
        contradiction
      have hh : runSteps (Source ks states symbols k p input output main initial inZero inOne).step n c' = some d := by
        rw [hs] at h
        exact h
      rw [runSteps_front, run_step ks states symbols k p input output main initial inZero inOne z one c hactive,hs]
      exact ih c' hh

set_option backward.isDefEq.respectTransparency false in
theorem aux_step (ks states symbols : Nat) (k : Nat) (p : Program)
    (input output main initial inZero inOne z one : Nat)
    (c : (Shared.ComplexityBridge.TM2AuxSweep.machine ks states symbols initial).Cfg)
    (h : c.l ≠ some Shared.ComplexityBridge.TM2AuxSweep.done) :
    (machine ks states symbols k p input output main initial inZero inOne z one).step (auxEmbed ks states symbols k p c) =
      ((Shared.ComplexityBridge.TM2AuxSweep.machine ks states symbols initial).step c).map (auxEmbed ks states symbols k p) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      have hl : l ≠ Shared.ComplexityBridge.TM2AuxSweep.done := by intro he; apply h; exact congrArg some he
      change some (stepAux (program ks states symbols initial k p input main inZero inOne output z one (auxLabel l)) (.inr v) S) = _
      simp only [program,auxLabel,if_neg hl]
      rw [liftAux_aux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem strict_step (ks states symbols : Nat) (k : Nat) (p : Program)
    (input output main initial inZero inOne z one : Nat)
    (c : (Shared.ComplexityBridge.TM2StrictCleanup.machine ks states symbols initial output z one).Cfg) (hactive : c.l ≠ none) :
    (machine ks states symbols k p input output main initial inZero inOne z one).step (strictEmbed ks states symbols k p c) =
      ((Shared.ComplexityBridge.TM2StrictCleanup.machine ks states symbols initial output z one).step c).map (strictEmbed ks states symbols k p) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => contradiction
    | some l =>
      change some (stepAux (liftStrict ks states symbols initial k p
        (Shared.ComplexityBridge.TM2StrictCleanup.program ks states symbols initial output z one l)) (.inr v)
          (strictStacks ks symbols S)) = _
      rw [liftStrict_aux]
      rfl

set_option backward.isDefEq.respectTransparency false in
theorem strict_run (ks states symbols : Nat) (k : Nat) (p : Program)
    (input output main initial inZero inOne z one : Nat)
    (n : Nat) (c d : (Shared.ComplexityBridge.TM2StrictCleanup.machine ks states symbols initial output z one).Cfg)
    (h : runSteps (Shared.ComplexityBridge.TM2StrictCleanup.machine ks states symbols initial output z one).step n c = some d) :
    runSteps (machine ks states symbols k p input output main initial inZero inOne z one).step n
      (strictEmbed ks states symbols k p c) = some (strictEmbed ks states symbols k p d) := by
  induction n generalizing c with
  | zero =>
    change some c = some d at h
    cases h
    rfl
  | succ n ih =>
    rw [runSteps_front] at h
    change ((Shared.ComplexityBridge.TM2StrictCleanup.machine ks states symbols initial output z one).step c).bind
      (runSteps (Shared.ComplexityBridge.TM2StrictCleanup.machine ks states symbols initial output z one).step n) = some d at h
    cases hs : (Shared.ComplexityBridge.TM2StrictCleanup.machine ks states symbols initial output z one).step c with
    | none => rw [hs] at h; contradiction
    | some c' =>
      have hactive : c.l ≠ none := by
        intro hl
        have hn : (Shared.ComplexityBridge.TM2StrictCleanup.machine ks states symbols initial output z one).step c = none := by
          cases c with
          | mk l v S => cases l with
            | none => rfl
            | some l => simp at hl
        rw [hn] at hs
        contradiction
      have hh : runSteps (Shared.ComplexityBridge.TM2StrictCleanup.machine ks states symbols initial output z one).step n c' = some d := by
        rw [hs] at h
        exact h
      rw [runSteps_front,strict_step ks states symbols k p input output main initial inZero inOne z one c hactive,hs]
      exact ih c' hh

theorem initial_eq (ks states symbols : Nat) (k : Nat) (p : Program)
    (input output main initial inZero inOne z one : Nat) (bits : List Bool) :
    Turing.initList (machine ks states symbols k p input output main initial inZero inOne z one) bits =
      runEmbed ks states symbols initial k p
        (Turing.initList (Source ks states symbols k p input output main initial inZero inOne) bits) := by
  rfl

theorem strict_halt (ks states symbols : Nat) (k : Nat) (p : Program)
    (input output main initial inZero inOne z one : Nat) (answer : Bool) :
    strictEmbed ks states symbols k p
      (Turing.haltList (Shared.ComplexityBridge.TM2StrictCleanup.machine ks states symbols initial output z one) [answer]) =
    Turing.haltList (machine ks states symbols k p input output main initial inZero inOne z one) [answer] := by
  change (Cfg.mk none (Sum.inl (Sum.inl (none,false))) _ :
    (machine ks states symbols k p input output main initial inZero inOne z one).Cfg) = Cfg.mk none (Sum.inl (Sum.inl (none,false))) _
  congr 1
  funext s
  cases s with
  | inl t =>
    cases t with
    | inl b => cases b <;> simp [strictStacks,Shared.ComplexityBridge.TM2StrictCleanup.machine,machine,Turing.haltList,Function.update]
    | inr q => cases q <;> simp [strictStacks,Shared.ComplexityBridge.TM2StrictCleanup.machine,machine,Turing.haltList,Function.update]
  | inr j => simp [strictStacks,Shared.ComplexityBridge.TM2StrictCleanup.machine,machine,Turing.haltList,Function.update]

def auxTerminal (ks states symbols : Nat) (c : (Shared.ComplexityBridge.TM2AuxSweep.machine ks states symbols 0).Cfg) : Prop :=
  c.l = some Shared.ComplexityBridge.TM2AuxSweep.done
noncomputable instance (ks states symbols : Nat) : DecidablePred (auxTerminal ks states symbols) := fun _ => Classical.propDecidable _

theorem aux_stable (ks states symbols initial : Nat) (c : (Shared.ComplexityBridge.TM2AuxSweep.machine ks states symbols initial).Cfg)
    (h : auxTerminal ks states symbols c) : (Shared.ComplexityBridge.TM2AuxSweep.machine ks states symbols initial).step c = some c := by
  cases c with
  | mk l v S =>
    change l = some Shared.ComplexityBridge.TM2AuxSweep.done at h
    subst l
    change some (stepAux (Shared.ComplexityBridge.TM2AuxSweep.program ks states symbols Shared.ComplexityBridge.TM2AuxSweep.done) v S) = _
    simp [Shared.ComplexityBridge.TM2AuxSweep.program,Shared.ComplexityBridge.TM2AuxSweep.done,stepAux]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- A complete auxiliary sweep is reproduced until the shared continuation. -/
theorem aux_run (ks states symbols : Nat) (k : Nat) (p : Program)
    (input output main initial inZero inOne z one : Nat) (answer : Bool) (v : Fin (states+1)) (flag : Bool)
    (a b : List Bool) (A : Shared.ComplexityBridge.TM2AuxSweep.Index → List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) (bound : Nat) (hb : ∀ i, (A i).length ≤ bound) :
    ∃ n ≤ 5*(bound+1), ∃ f,
      runSteps (machine ks states symbols k p input output main initial inZero inOne z one).step n
        (auxEmbed ks states symbols k p (Shared.ComplexityBridge.TM2AuxSweep.cfg ks states symbols initial
          ⟨0,by decide⟩ answer v flag a b A S)) =
      some (auxEmbed ks states symbols k p (Shared.ComplexityBridge.TM2AuxSweep.cfg ks states symbols initial
        Shared.ComplexityBridge.TM2AuxSweep.done answer v f a b (fun _ => []) S)) := by
  obtain ⟨m,hm,f,hr⟩ := Shared.ComplexityBridge.TM2AuxSweep.sweep_from_start ks states symbols initial answer v flag a b A S bound hb
  letI : DecidablePred (auxTerminal ks states symbols) := fun _ => Classical.propDecidable _
  obtain ⟨n,hn,hr'⟩ := Shared.ComplexityBridge.TM2UnaryTransfer.run_to_stable_lift
    (Shared.ComplexityBridge.TM2AuxSweep.machine ks states symbols initial).step
    (machine ks states symbols k p input output main initial inZero inOne z one).step
    (auxEmbed ks states symbols k p) (auxTerminal ks states symbols) (aux_stable ks states symbols initial)
    (aux_step ks states symbols k p input output main initial inZero inOne z one) m _ _ (by rfl) hr
  exact ⟨n,le_trans hn hm,f,hr'⟩

theorem aux_dispatch_true (ks states symbols : Nat) (k : Nat) (p : Program)
    (input output main initial inZero inOne z one : Nat) (v : Fin (states+1)) (flag : Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (machine ks states symbols k p input output main initial inZero inOne z one).step
      (auxEmbed ks states symbols k p (Shared.ComplexityBridge.TM2AuxSweep.cfg ks states symbols initial
        Shared.ComplexityBridge.TM2AuxSweep.done true v flag [] [] (fun _ => []) S)) =
    some (strictEmbed ks states symbols k p (Shared.ComplexityBridge.TM2StrictCleanup.fetch ks states symbols initial output z one v S)) := by
  change some (stepAux (program ks states symbols initial k p input main inZero inOne output z one
    (auxLabel Shared.ComplexityBridge.TM2AuxSweep.done)) (.inr (true,v,flag))
      (Shared.ComplexityBridge.TM2AuxSweep.stackVals ks symbols [] [] (fun _ => []) S)) = _
  simp only [program,auxLabel,ite_true,stepAux,cleanState,Bool.cond_true,Bool.cond_false]
  congr 1
  congr 1
  funext j
  cases j with
  | inl t => cases t with
    | inl b => cases b <;> rfl
    | inr q => cases q <;> rfl
  | inr j => rfl

theorem aux_dispatch_false (ks states symbols : Nat) (k : Nat) (p : Program)
    (input output main initial inZero inOne z one : Nat) (v : Fin (states+1)) (flag : Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    (machine ks states symbols k p input output main initial inZero inOne z one).step
      (auxEmbed ks states symbols k p (Shared.ComplexityBridge.TM2AuxSweep.cfg ks states symbols initial
        Shared.ComplexityBridge.TM2AuxSweep.done false v flag [] [] (fun _ => []) S)) =
    some (strictEmbed ks states symbols k p (Shared.ComplexityBridge.TM2StrictCleanup.embed ks states symbols
      (Shared.ComplexityBridge.TM2Cleanup.cfg ks states symbols initial ⟨0,by omega⟩ false v false S))) := by
  change some (stepAux (program ks states symbols initial k p input main inZero inOne output z one
    (auxLabel Shared.ComplexityBridge.TM2AuxSweep.done)) (.inr (false,v,flag))
      (Shared.ComplexityBridge.TM2AuxSweep.stackVals ks symbols [] [] (fun _ => []) S)) = _
  simp only [program,auxLabel,ite_true,stepAux,cleanState,Bool.cond_true,Bool.cond_false]
  congr 1
  congr 1
  funext j
  cases j with
  | inl t => cases t with
    | inl b => cases b <;> rfl
    | inr q => cases q <;> rfl
  | inr j => rfl

def auxValues (ticks : List Bool) (b : Nat) : Shared.ComplexityBridge.TM2AuxSweep.Index → List Bool :=
  fun i => if i.val = 0 then ticks else if i.val = 1 then List.replicate b true else []

/-- A source halt is exactly the start of the auxiliary sweep, with the clock
flag retained as the success/timeout discriminator. -/
theorem halted_to_aux (ks states symbols : Nat) (k : Nat) (p : Program) (initial : Nat)
    (b : Nat) (flag : Option Bool) (ticks : List Bool)
    (c : Cfg (fun _ : Fin (ks+1) => Fin (symbols+1)) (Fin (p.length+1)) (Fin (states+1)))
    (hh : c.l = none) :
    runEmbed ks states symbols initial k p
      (Shared.ComplexityBridge.TM2PairClock.runnerEmbed ks states symbols k p (Shared.ComplexityBridge.TM2PairClock.aux b)
        (Shared.ComplexityBridge.TM2LoadedClock.clockEmbed ks states symbols p []
          (Shared.ComplexityBridge.TM2UnaryClock.embed ks states symbols p.length flag ticks c))) =
    auxEmbed ks states symbols k p (Shared.ComplexityBridge.TM2AuxSweep.cfg ks states symbols initial
      ⟨0,by decide⟩ flag.isSome c.var false [] [] (auxValues ticks b) c.stk) := by
  cases c with
  | mk l v S =>
    cases l with
    | some l => simp at hh
    | none =>
      change (Cfg.mk (some beginAux) (Sum.inr (flag.isSome,v,false)) _ : Cfg (Alphabet ks symbols) (Label ks k p) (State states)) =
        Cfg.mk (some beginAux) (Sum.inr (flag.isSome,v,false)) _
      congr 1
      funext j
      cases j with
      | inl t =>
        cases t with
        | inl x => cases x <;> rfl
        | inr q => cases q <;> simp [Shared.ComplexityBridge.TM2PairClock.runnerEmbed,
            Shared.ComplexityBridge.TM2LoadedClock.clockEmbed,Shared.ComplexityBridge.TM2UnaryClock.embed,
            Shared.ComplexityBridge.TM2Combined.embedCfg,Shared.ComplexityBridge.TM2AuxSweep.cfg,
            Shared.ComplexityBridge.TM2PairClock.runnerStacks,
            Shared.ComplexityBridge.TM2PairClock.aux,Shared.ComplexityBridge.TM2UnaryMultiply.stackVals,
            Shared.ComplexityBridge.TM2LoadedClock.clockStacks,Shared.ComplexityBridge.TM2Combined.embedStacks,
            Shared.ComplexityBridge.TM2AuxSweep.stackVals,Shared.ComplexityBridge.TM2AuxSweep.stackIndex,auxValues] <;> rfl
      | inr j => rfl

theorem auxValues_bound (ticks : List Bool) (b bound : Nat) (ht : ticks.length ≤ bound) (hb : b ≤ bound) :
    ∀ i, (auxValues ticks b i).length ≤ bound := by
  intro i
  fin_cases i <;> simp [auxValues,ht,hb]

set_option backward.isDefEq.respectTransparency false in
/-- Normal halt: clear arithmetic stacks, strictly decode the core output,
clear the core stacks and halt with a canonical Boolean output. -/
theorem cleanup_true (ks states symbols : Nat) (k : Nat) (p : Program)
    (input output main initial inZero inOne z one : Nat) (v : Fin (states+1))
    (A : Shared.ComplexityBridge.TM2AuxSweep.Index → List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) (abound sbound : Nat)
    (ha : ∀ i, (A i).length ≤ abound) (hs : ∀ j, (S j).length ≤ sbound) :
    ∃ n ≤ 5*(abound+1)+1+(ks+1)*(sbound+1)+3,
      runSteps (machine ks states symbols k p input output main initial inZero inOne z one).step n
        (auxEmbed ks states symbols k p (Shared.ComplexityBridge.TM2AuxSweep.cfg ks states symbols initial
          ⟨0,by decide⟩ true v false [] [] A S)) =
      some (Turing.haltList (machine ks states symbols k p input output main initial inZero inOne z one)
        [(Shared.ComplexityBridge.TM2BooleanOutput.decodeStack (z,one,(S (clip ks output)).map Fin.val)).getD false]) := by
  obtain ⟨a,ha',flag,haux⟩ := aux_run ks states symbols k p input output main initial inZero inOne z one
    true v false [] [] A S abound ha
  obtain ⟨t,ht,hclean⟩ := Shared.ComplexityBridge.TM2StrictCleanup.strict_read_and_clean ks states symbols initial output z one v S sbound hs
  have hr := strict_run ks states symbols k p input output main initial inZero inOne z one t
    (Shared.ComplexityBridge.TM2StrictCleanup.fetch ks states symbols initial output z one v S)
    (Turing.haltList (Shared.ComplexityBridge.TM2StrictCleanup.machine ks states symbols initial output z one)
      [(Shared.ComplexityBridge.TM2BooleanOutput.decodeStack (z,one,(S (clip ks output)).map Fin.val)).getD false]) hclean
  rw [strict_halt] at hr
  refine ⟨a+1+t,by omega,?_⟩
  have hn : a+1+t = a+(t+1) := by omega
  rw [hn,runSteps_add,haux]
  change runSteps (machine ks states symbols k p input output main initial inZero inOne z one).step (t+1)
    (auxEmbed ks states symbols k p (Shared.ComplexityBridge.TM2AuxSweep.cfg ks states symbols initial
      Shared.ComplexityBridge.TM2AuxSweep.done true v flag [] [] (fun _ => []) S)) = _
  rw [runSteps_front,aux_dispatch_true]
  exact hr

set_option backward.isDefEq.respectTransparency false in
/-- Timeout: skip output decoding entirely, clear all stacks, and return false. -/
theorem cleanup_false (ks states symbols : Nat) (k : Nat) (p : Program)
    (input output main initial inZero inOne z one : Nat) (v : Fin (states+1))
    (A : Shared.ComplexityBridge.TM2AuxSweep.Index → List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) (abound sbound : Nat)
    (ha : ∀ i, (A i).length ≤ abound) (hs : ∀ j, (S j).length ≤ sbound) :
    ∃ n ≤ 5*(abound+1)+1+(ks+1)*(sbound+1)+1,
      runSteps (machine ks states symbols k p input output main initial inZero inOne z one).step n
        (auxEmbed ks states symbols k p (Shared.ComplexityBridge.TM2AuxSweep.cfg ks states symbols initial
          ⟨0,by decide⟩ false v false [] [] A S)) =
      some (Turing.haltList (machine ks states symbols k p input output main initial inZero inOne z one) [false]) := by
  obtain ⟨a,ha',flag,haux⟩ := aux_run ks states symbols k p input output main initial inZero inOne z one
    false v false [] [] A S abound ha
  obtain ⟨t,ht,hclean⟩ := Shared.ComplexityBridge.TM2Cleanup.sweep_all ks states symbols initial false v false S sbound hs
  have hstrict := Shared.ComplexityBridge.TM2StrictCleanup.sweep_run ks states symbols initial output z one
    (Shared.ComplexityBridge.TM2Cleanup.cfg ks states symbols initial ⟨0,by omega⟩ false v false S) t
  rw [hclean] at hstrict
  change runSteps (Shared.ComplexityBridge.TM2StrictCleanup.machine ks states symbols initial output z one).step t
    (Shared.ComplexityBridge.TM2StrictCleanup.embed ks states symbols (Shared.ComplexityBridge.TM2Cleanup.cfg ks states symbols initial ⟨0,by omega⟩ false v false S)) =
      some (Shared.ComplexityBridge.TM2StrictCleanup.embed ks states symbols
        (Turing.haltList (Shared.ComplexityBridge.TM2Cleanup.cleaner ks states symbols initial) [false])) at hstrict
  rw [Shared.ComplexityBridge.TM2StrictCleanup.embed_halt ks states symbols initial output z one] at hstrict
  have hr := strict_run ks states symbols k p input output main initial inZero inOne z one t
    (Shared.ComplexityBridge.TM2StrictCleanup.embed ks states symbols (Shared.ComplexityBridge.TM2Cleanup.cfg ks states symbols initial ⟨0,by omega⟩ false v false S))
    (Turing.haltList (Shared.ComplexityBridge.TM2StrictCleanup.machine ks states symbols initial output z one) [false]) hstrict
  rw [strict_halt] at hr
  refine ⟨a+1+t,by omega,?_⟩
  have hn : a+1+t = a+(t+1) := by omega
  rw [hn,runSteps_add,haux]
  change runSteps (machine ks states symbols k p input output main initial inZero inOne z one).step (t+1)
    (auxEmbed ks states symbols k p (Shared.ComplexityBridge.TM2AuxSweep.cfg ks states symbols initial
      Shared.ComplexityBridge.TM2AuxSweep.done false v flag [] [] (fun _ => []) S)) = _
  rw [runSteps_front,aux_dispatch_false]
  exact hr

set_option backward.isDefEq.respectTransparency false in
/-- One actual machine starts on the canonical pair, runs the exact bounded
candidate, strictly decodes any halted output, cleans every stack, and halts
in the library's Boolean-output configuration. -/
theorem pair_halt_total (d : Shared.ComplexityBridge.TM2BooleanInput.InputData)
    (k : Nat) (p : Program) (output z one : Nat) (x w : List Bool)
    (hdata : Shared.ComplexityBridge.TM2BooleanInput.validInputData d = true) (hmain : d.main < p.length)
    (hp : programValid p d.stackCount d.states d.symbols = true) (hout : output < d.stackCount)
    (start result : Shared.Codes.TM2StatementExecution.Result)
    (hstart : Shared.ComplexityBridge.TM2BooleanInput.buildStart d (BitstringEncoding.bitEncode (x,w)) = some start)
    (hrun : run p ((x.length+w.length+2)^k) start = .halted result) :
    ∃ n ≤ (4*(BitstringEncoding.bitEncode (x,w)).length+8 + k*14*(x.length+w.length+4)^k + (x.length+w.length+2)^k) +
      (5*((x.length+w.length+2)^k+(x.length+w.length+2)+1)+1 +
        (d.stackCount+1)*((BitstringEncoding.bitEncode (x,w)).length+(x.length+w.length+2)^k*
          Shared.ComplexityBridge.TM2StackBound.programDepth p+1)+3),
      runSteps (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol z one).step n
        (Turing.initList (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol z one)
          (BitstringEncoding.bitEncode (x,w))) =
      some (Turing.haltList (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol z one)
        [(Shared.ComplexityBridge.TM2BooleanOutput.extractMemory (z,one,output,result.label,result.memory)).getD false]) := by
  let bits := BitstringEncoding.bitEncode (x,w)
  let b := x.length+w.length+2
  let fuel := b^k
  let ab := fuel+b
  let sb := bits.length+fuel*Shared.ComplexityBridge.TM2StackBound.programDepth p
  obtain ⟨start',hs,hvalid⟩ := Shared.ComplexityBridge.TM2FiniteBoundary.buildStart_valid d bits p hdata hmain
  have heq : start' = start := Option.some.inj (hs.symm.trans hstart)
  subst start'
  obtain ⟨a,ha,m,hm,c',hrel,hh,hsource⟩ :=
    Shared.ComplexityBridge.TM2ClockFlag.pair_numeric_halt_true d k p output x w hdata hp start result hstart hvalid hrun
  have hsource' := run_run d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol z one a _ _ hsource
  have hsafe := Shared.Codes.TM2Program.run_safe p d.stackCount d.states d.symbols hp fuel start hvalid
  rw [hrun] at hsafe
  have hbound := Shared.ComplexityBridge.TM2StackBound.run_from_input_bound d bits p fuel start hstart
  rw [hrun] at hbound
  have hS := Shared.ComplexityBridge.TM2StackBound.related_stack_bound d.stackCount d.states d.symbols p.length
    c' result hrel sb hbound
  let ticks := (List.replicate fuel true).drop m
  have ht : ticks.length ≤ ab := by
    dsimp [ticks,ab]
    simp only [List.length_drop,List.length_replicate]
    omega
  have hb : b ≤ ab := by dsimp [ab]; omega
  have hA := auxValues_bound ticks b ab ht hb
  obtain ⟨t,htime,hclean⟩ := cleanup_true d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol z one c'.var (auxValues ticks b) c'.stk ab sb hA hS
  have hdecode : (Shared.ComplexityBridge.TM2BooleanOutput.decodeStack
      (z,one,(c'.stk (clip d.stackCount output)).map Fin.val)).getD false =
      (Shared.ComplexityBridge.TM2BooleanOutput.extractMemory (z,one,output,result.label,result.memory)).getD false := by
    rw [← Shared.ComplexityBridge.TM2StrictCleanup.strictAnswer_eq]
    exact Shared.ComplexityBridge.TM2VerifierValidity.strict_related d.stackCount d.states d.symbols p.length z one output result c' hrel hout hsafe.2
  rw [hdecode] at hclean
  refine ⟨a+t,by dsimp [bits,b,fuel,ab,sb] at *; omega,?_⟩
  rw [initial_eq,runSteps_add,hsource']
  change runSteps (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol z one).step t
    (runEmbed d.stackCount d.states d.symbols d.initialState k p
      (Shared.ComplexityBridge.TM2PairClock.runnerEmbed d.stackCount d.states d.symbols k p (Shared.ComplexityBridge.TM2PairClock.aux b)
        (Shared.ComplexityBridge.TM2LoadedClock.clockEmbed d.stackCount d.states d.symbols p []
          (Shared.ComplexityBridge.TM2UnaryClock.embed d.stackCount d.states d.symbols p.length (some true) ticks c')))) = _
  rw [halted_to_aux d.stackCount d.states d.symbols k p d.initialState b (some true) ticks c' hh]
  exact hclean

/-- The clock timeout takes one source block to its ordinary halted state,
retaining `none` as the clock flag. -/
theorem timeout_source_next (d : Shared.ComplexityBridge.TM2BooleanInput.InputData)
    (k : Nat) (p : Program) (output b : Nat)
    (c : Cfg (fun _ : Fin (d.stackCount+1) => Fin (d.symbols+1)) (Fin (p.length+1)) (Fin (d.states+1))) :
    (Source d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol).step
      (Shared.ComplexityBridge.TM2PairClock.runnerEmbed d.stackCount d.states d.symbols k p (Shared.ComplexityBridge.TM2PairClock.aux b)
        (Shared.ComplexityBridge.TM2LoadedClock.clockEmbed d.stackCount d.states d.symbols p []
          (Shared.ComplexityBridge.TM2UnaryClock.timeoutCfg d.stackCount d.states d.symbols p.length c))) =
    some (Shared.ComplexityBridge.TM2PairClock.runnerEmbed d.stackCount d.states d.symbols k p (Shared.ComplexityBridge.TM2PairClock.aux b)
      (Shared.ComplexityBridge.TM2LoadedClock.clockEmbed d.stackCount d.states d.symbols p []
        (Shared.ComplexityBridge.TM2UnaryClock.embed d.stackCount d.states d.symbols p.length none []
          ⟨none,c.var,c.stk⟩))) := by rfl

set_option backward.isDefEq.respectTransparency false in
/-- A timeout always returns false after the exact input-driven clock, even if
the unfinished candidate's output stack happens to contain the true code. -/
theorem pair_timeout_total (d : Shared.ComplexityBridge.TM2BooleanInput.InputData)
    (k : Nat) (p : Program) (output z one : Nat) (x w : List Bool)
    (hdata : Shared.ComplexityBridge.TM2BooleanInput.validInputData d = true) (hmain : d.main < p.length)
    (hp : programValid p d.stackCount d.states d.symbols = true)
    (start result : Shared.Codes.TM2StatementExecution.Result)
    (hstart : Shared.ComplexityBridge.TM2BooleanInput.buildStart d (BitstringEncoding.bitEncode (x,w)) = some start)
    (hrun : run p ((x.length+w.length+2)^k) start = .timeout result) :
    ∃ n ≤ (4*(BitstringEncoding.bitEncode (x,w)).length+9 + k*14*(x.length+w.length+4)^k + (x.length+w.length+2)^k) + 1 +
      (5*((x.length+w.length+2)^k+(x.length+w.length+2)+1)+1 +
        (d.stackCount+1)*((BitstringEncoding.bitEncode (x,w)).length+(x.length+w.length+2)^k*
          Shared.ComplexityBridge.TM2StackBound.programDepth p+1)+1),
      runSteps (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol z one).step n
        (Turing.initList (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol z one)
          (BitstringEncoding.bitEncode (x,w))) =
      some (Turing.haltList (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol z one) [false]) := by
  let bits := BitstringEncoding.bitEncode (x,w)
  let b := x.length+w.length+2
  let fuel := b^k
  let ab := fuel+b
  let sb := bits.length+fuel*Shared.ComplexityBridge.TM2StackBound.programDepth p
  obtain ⟨start',hs,hvalid⟩ := Shared.ComplexityBridge.TM2FiniteBoundary.buildStart_valid d bits p hdata hmain
  have heq : start' = start := Option.some.inj (hs.symm.trans hstart)
  subst start'
  obtain ⟨a,ha,c',hrel,hsource⟩ :=
    Shared.ComplexityBridge.TM2PairClock.pair_numeric_timeout d k p output x w hdata hp start result hstart hvalid hrun
  have hsource' := run_run d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol z one a _ _ hsource
  have hbound := Shared.ComplexityBridge.TM2StackBound.run_from_input_bound d bits p fuel start hstart
  rw [hrun] at hbound
  have hS := Shared.ComplexityBridge.TM2StackBound.related_stack_bound d.stackCount d.states d.symbols p.length
    c' result hrel sb hbound
  have hA := auxValues_bound [] b ab (by dsimp [ab]; simp) (by dsimp [ab]; omega)
  obtain ⟨t,htime,hclean⟩ := cleanup_false d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState
    d.falseSymbol d.trueSymbol z one c'.var (auxValues [] b) c'.stk ab sb hA hS
  let ct := Shared.ComplexityBridge.TM2PairClock.runnerEmbed d.stackCount d.states d.symbols k p (Shared.ComplexityBridge.TM2PairClock.aux b)
    (Shared.ComplexityBridge.TM2LoadedClock.clockEmbed d.stackCount d.states d.symbols p []
      (Shared.ComplexityBridge.TM2UnaryClock.timeoutCfg d.stackCount d.states d.symbols p.length c'))
  let cn : Cfg (fun _ : Fin (d.stackCount+1) => Fin (d.symbols+1)) (Fin (p.length+1)) (Fin (d.states+1)) := ⟨none,c'.var,c'.stk⟩
  let cf := Shared.ComplexityBridge.TM2PairClock.runnerEmbed d.stackCount d.states d.symbols k p (Shared.ComplexityBridge.TM2PairClock.aux b)
    (Shared.ComplexityBridge.TM2LoadedClock.clockEmbed d.stackCount d.states d.symbols p []
      (Shared.ComplexityBridge.TM2UnaryClock.embed d.stackCount d.states d.symbols p.length none [] cn))
  have hnext : (Source d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol).step ct = some cf :=
    timeout_source_next d k p output b c'
  have hactive : ct.l ≠ none := by dsimp [ct,Shared.ComplexityBridge.TM2PairClock.runnerEmbed,Shared.ComplexityBridge.TM2LoadedClock.clockEmbed,Shared.ComplexityBridge.TM2UnaryClock.timeoutCfg]; simp
  have hone := run_step d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol z one ct hactive
  rw [hnext] at hone
  change (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol z one).step
    (runEmbed d.stackCount d.states d.symbols d.initialState k p ct) =
      some (runEmbed d.stackCount d.states d.symbols d.initialState k p cf) at hone
  have hcn : cn.l = none := rfl
  have haux : runEmbed d.stackCount d.states d.symbols d.initialState k p cf =
      auxEmbed d.stackCount d.states d.symbols k p (Shared.ComplexityBridge.TM2AuxSweep.cfg d.stackCount d.states d.symbols d.initialState
        ⟨0,by decide⟩ false c'.var false [] [] (auxValues [] b) c'.stk) := by
    exact halted_to_aux d.stackCount d.states d.symbols k p d.initialState b none [] cn hcn
  rw [haux] at hone
  refine ⟨a+1+t,by dsimp [bits,b,fuel,ab,sb] at *; omega,?_⟩
  have hn : a+1+t = a+(t+1) := by omega
  rw [initial_eq,hn,runSteps_add,hsource']
  change runSteps (machine d.stackCount d.states d.symbols k p d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol z one).step (t+1)
    (runEmbed d.stackCount d.states d.symbols d.initialState k p ct) = _
  rw [runSteps_front,hone]
  exact hclean

/-- A timed-out program leaves the true code on its output stack; the totalizer
must nevertheless return false. -/
example : (runSteps (machine 2 1 2 0 [.push 1 [1] (.goto [0])] 0 1 0 0 0 1 0 1).step 29
    (Turing.initList (machine 2 1 2 0 [.push 1 [1] (.goto [0])] 0 1 0 0 0 1 0 1)
      (BitstringEncoding.bitEncode (([] : List Bool), ([] : List Bool))))).map
      (fun c => c.stk (.inl (.inl true))) = some [false] := by
  change (Option.map (fun c => c.stk (.inl (.inl true)))
    (runSteps (machine 2 1 2 0 [.push 1 [1] (.goto [0])] 0 1 0 0 0 1 0 1).step 29
      (Turing.initList (machine 2 1 2 0 [.push 1 [1] (.goto [0])] 0 1 0 0 0 1 0 1)
        (BitstringEncoding.bitEncode (([] : List Bool), ([] : List Bool))))) : Option (List Bool)) = some [false]
  decide

/-- A genuine halt with a singleton true output survives the same cleanup. -/
example : (runSteps (machine 2 1 2 0 [.push 1 [1] .halt] 0 1 0 0 0 1 0 1).step 28
    (Turing.initList (machine 2 1 2 0 [.push 1 [1] .halt] 0 1 0 0 0 1 0 1)
      (BitstringEncoding.bitEncode (([] : List Bool), ([] : List Bool))))).map
      (fun c => c.stk (.inl (.inl true))) = some [true] := by
  change (Option.map (fun c => c.stk (.inl (.inl true)))
    (runSteps (machine 2 1 2 0 [.push 1 [1] .halt] 0 1 0 0 0 1 0 1).step 28
      (Turing.initList (machine 2 1 2 0 [.push 1 [1] .halt] 0 1 0 0 0 1 0 1)
        (BitstringEncoding.bitEncode (([] : List Bool), ([] : List Bool))))) : Option (List Bool)) = some [true]
  decide

end Shared.ComplexityBridge.TM2PairTotalizer
