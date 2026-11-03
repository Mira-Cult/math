import Shared.ComplexityBridge.TM2IgnoreWitness

namespace Shared.ComplexityBridge.TM2UnaryClock
open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.ComplexityBridge.TM2Combined
open Shared.ComplexityBridge.TM2FiniteReverse Shared.Codes.TM2Program
open Shared.Codes.TM2StatementExecution Shared.Codes.TM2StatementValidation

def program (ks states symbols : Nat) (p : Program) : Bool ⊕ Fin (p.length+1) →
    Stmt (Alphabet ks symbols) (Bool ⊕ Fin (p.length+1)) (Option Bool × Fin (states+1))
  | .inl _ => .halt
  | .inr l => .pop (.inl false) (fun v h => (h,v.2))
      (.branch (fun v => v.1.isSome) (liftStmt ks states symbols p.length (finiteProgram ks states symbols p l))
        (.goto (fun _ => .inl false)))

def clocked (ks states symbols : Nat) (p : Program) (input output main initial : Nat) : Turing.FinTM2 where
  K := Bool ⊕ Fin (ks+1)
  k₀ := .inr (clip ks input)
  k₁ := .inr (clip ks output)
  Γ := Alphabet ks symbols
  Λ := Bool ⊕ Fin (p.length+1)
  main := .inr (clip p.length main)
  σ := Option Bool × Fin (states+1)
  initialState := (none,clip states initial)
  Γk₀Fin := inferInstanceAs (Fintype (Fin (symbols+1)))
  m := program ks states symbols p

/-- A machine-independent encoding of an active or halted core configuration
with a separate finite unary-clock stack. The second auxiliary stack is empty. -/
def embed (ks states symbols labels : Nat) (flag : Option Bool) (ticks : List Bool)
    (c : Cfg (fun _ : Fin (ks+1) => Fin (symbols+1)) (Fin (labels+1)) (Fin (states+1))) :
    Cfg (Alphabet ks symbols) (Bool ⊕ Fin (labels+1)) (Option Bool × Fin (states+1)) :=
  embedCfg ks states symbols labels flag ticks [] c

def timeoutCfg (ks states symbols labels : Nat)
    (c : Cfg (fun _ : Fin (ks+1) => Fin (symbols+1)) (Fin (labels+1)) (Fin (states+1))) :
    Cfg (Alphabet ks symbols) (Bool ⊕ Fin (labels+1)) (Option Bool × Fin (states+1)) :=
  ⟨some (.inl false),(none,c.var),embedStacks ks symbols [] [] c.stk⟩

theorem pop_clock (ks symbols : Nat) (x : Bool) (xs : List Bool)
    (S : Fin (ks+1) → List (Fin (symbols+1))) :
    Function.update (embedStacks ks symbols (x::xs) [] S) (.inl false) xs = embedStacks ks symbols xs [] S := by
  funext k
  cases k with
  | inl b => cases b <;> simp [embedStacks,Function.update]
  | inr j => simp [embedStacks,Function.update]

theorem pop_empty_clock (ks symbols : Nat) (S : Fin (ks+1) → List (Fin (symbols+1))) :
    Function.update (embedStacks ks symbols [] [] S) (.inl false) [] = embedStacks ks symbols [] [] S := by
  funext k
  cases k with
  | inl b => cases b <;> simp [embedStacks,Function.update]
  | inr j => simp [embedStacks,Function.update]

set_option backward.isDefEq.respectTransparency false in
/-- One tick executes exactly one whole core statement block. -/
theorem step_tick (ks states symbols : Nat) (p : Program) (input output main initial : Nat)
    (c d : (finiteCore ks states symbols p input output main initial).Cfg)
    (flag : Option Bool) (x : Bool) (ticks : List Bool)
    (h : (finiteCore ks states symbols p input output main initial).step c = some d) :
    (clocked ks states symbols p input output main initial).step (embed ks states symbols p.length flag (x::ticks) c) =
      some (embed ks states symbols p.length (some x) ticks d) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => simp [Turing.FinTM2.step,Turing.TM2.step] at h
    | some l =>
      have hd : stepAux (finiteProgram ks states symbols p l) v S = d := by
        simpa [Turing.FinTM2.step,Turing.TM2.step,finiteCore] using h
      change some (stepAux (liftStmt ks states symbols p.length (finiteProgram ks states symbols p l)) (some x,v)
        (Function.update (embedStacks ks symbols (x::ticks) [] S) (.inl false) ticks)) =
          some (embed ks states symbols p.length (some x) ticks d)
      rw [pop_clock,lift_stepAux,hd]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- A pending core step with no tick goes to an explicit timeout label, with
all core stacks and the core control value preserved. -/
theorem step_timeout (ks states symbols : Nat) (p : Program) (input output main initial : Nat)
    (c : (finiteCore ks states symbols p input output main initial).Cfg)
    (flag : Option Bool) (hactive : c.l ≠ none) :
    (clocked ks states symbols p input output main initial).step (embed ks states symbols p.length flag [] c) =
      some (timeoutCfg ks states symbols p.length c) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => contradiction
    | some l =>
      change some (Cfg.mk (some (Sum.inl false : Bool ⊕ Fin (p.length+1))) (none,v)
        (Function.update (embedStacks ks symbols [] [] S) (.inl false) [])) =
          some (Cfg.mk (some (Sum.inl false : Bool ⊕ Fin (p.length+1))) (none,v) (embedStacks ks symbols [] [] S))
      rw [pop_empty_clock]

set_option backward.isDefEq.respectTransparency false in
/-- Any successful finite core run of length at most the available clock is
mirrored with exactly one tick consumed per block. -/
theorem run_ticks (ks states symbols : Nat) (p : Program) (input output main initial : Nat)
    (n : Nat) (c d : (finiteCore ks states symbols p input output main initial).Cfg)
    (flag : Option Bool) (ticks : List Bool) (hlen : n ≤ ticks.length)
    (hrun : runSteps (finiteCore ks states symbols p input output main initial).step n c = some d) :
    ∃ flag', runSteps (clocked ks states symbols p input output main initial).step n
      (embed ks states symbols p.length flag ticks c) =
        some (embed ks states symbols p.length flag' (ticks.drop n) d) := by
  induction n generalizing c ticks flag with
  | zero =>
    change some c = some d at hrun
    cases hrun
    exact ⟨flag,by simp [runSteps]⟩
  | succ n ih =>
    cases ticks with
    | nil => simp at hlen
    | cons x ticks =>
      have hlen' : n ≤ ticks.length := by simp at hlen; omega
      rw [runSteps_front] at hrun
      change ((finiteCore ks states symbols p input output main initial).step c).bind
        (runSteps (finiteCore ks states symbols p input output main initial).step n) = some d at hrun
      cases hs : (finiteCore ks states symbols p input output main initial).step c with
      | none => rw [hs] at hrun; contradiction
      | some c' =>
        have hrest : runSteps (finiteCore ks states symbols p input output main initial).step n c' = some d := by
          rw [hs] at hrun
          exact hrun
        obtain ⟨flag',hclock⟩ := ih c' (some x) ticks hlen' hrest
        refine ⟨flag',?_⟩
        rw [runSteps_front,step_tick ks states symbols p input output main initial c c' flag x ticks hs]
        simpa using hclock

set_option backward.isDefEq.respectTransparency false in
/-- If the core has used all its ticks and still has a next block, the
following clocked block reaches timeout rather than continuing or stalling. -/
theorem run_timeout (ks states symbols : Nat) (p : Program) (input output main initial : Nat)
    (n : Nat) (c d : (finiteCore ks states symbols p input output main initial).Cfg)
    (flag : Option Bool) (ticks : List Bool) (hlen : ticks.length = n)
    (hrun : runSteps (finiteCore ks states symbols p input output main initial).step n c = some d)
    (hactive : d.l ≠ none) :
    runSteps (clocked ks states symbols p input output main initial).step (n+1)
      (embed ks states symbols p.length flag ticks c) = some (timeoutCfg ks states symbols p.length d) := by
  obtain ⟨flag',hclock⟩ := run_ticks ks states symbols p input output main initial n c d flag ticks (by omega) hrun
  have hdrop : ticks.drop n = [] := List.drop_eq_nil_of_le (by omega)
  rw [hdrop] at hclock
  rw [runSteps_add,hclock]
  change (clocked ks states symbols p input output main initial).step (embed ks states symbols p.length flag' [] d) = _
  exact step_timeout ks states symbols p input output main initial d flag' hactive

/-- The timeout configuration is an active, distinct control label; it is not
itself an ordinary halted configuration. -/
theorem timeout_is_active (ks states symbols labels : Nat)
    (c : Cfg (fun _ : Fin (ks+1) => Fin (symbols+1)) (Fin (labels+1)) (Fin (states+1))) :
    (timeoutCfg ks states symbols labels c).l = some (.inl false) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The checked numeric timeout outcome reaches the explicit timeout label
one block after its last permitted core block. -/
theorem numeric_timeout (ks states symbols : Nat) (p : Program) (input output main initial fuel : Nat)
    (hp : programValid p ks states symbols = true) (start result : Result)
    (hvalid : resultValid ks states symbols p.length start)
    (hrun : run p fuel start = .timeout result) :
    ∃ c', CfgRel ks states symbols p.length c' (erase result) ∧
      runSteps (clocked ks states symbols p input output main initial).step (fuel+1)
        (embed ks states symbols p.length none (List.replicate fuel true)
          (finiteConfig ks states symbols p.length start)) = some (timeoutCfg ks states symbols p.length c') := by
  have hfinite := finite_run_from_config ks states symbols p input output main initial hp fuel start hvalid
  rw [hrun] at hfinite
  obtain ⟨c',hc,hrel⟩ := hfinite
  have hsafe := run_safe p ks states symbols hp fuel start hvalid
  rw [hrun] at hsafe
  have hactive : c'.l ≠ none := by
    intro hn
    have hl := hrel.1
    change result.label = c'.l.map Fin.val at hl
    rw [hn] at hl
    have hnone : result.label = none := by simpa [Option.map] using hl
    exact hsafe.2 hnone
  refine ⟨c',hrel,?_⟩
  exact run_timeout ks states symbols p input output main initial fuel
    (finiteConfig ks states symbols p.length start) c' none (List.replicate fuel true) (by simp) hc hactive

set_option backward.isDefEq.respectTransparency false in
/-- A checked numeric halt within the clock is reproduced without an extra
core step; unused ticks remain on the clock stack. -/
theorem numeric_halt (ks states symbols : Nat) (p : Program) (input output main initial fuel : Nat)
    (hp : programValid p ks states symbols = true) (start result : Result)
    (hvalid : resultValid ks states symbols p.length start)
    (hrun : run p fuel start = .halted result) :
    ∃ n ≤ fuel, ∃ c' flag', CfgRel ks states symbols p.length c' (erase result) ∧ c'.l = none ∧
      runSteps (clocked ks states symbols p input output main initial).step n
        (embed ks states symbols p.length none (List.replicate fuel true)
          (finiteConfig ks states symbols p.length start)) =
            some (embed ks states symbols p.length flag' ((List.replicate fuel true).drop n) c') := by
  have hfinite := finite_run_from_config ks states symbols p input output main initial hp fuel start hvalid
  rw [hrun] at hfinite
  obtain ⟨n,hn,c',hc,hrel,hh⟩ := hfinite
  obtain ⟨flag',hclock⟩ := run_ticks ks states symbols p input output main initial n
    (finiteConfig ks states symbols p.length start) c' none (List.replicate fuel true) (by simpa using hn) hc
  exact ⟨n,hn,c',flag',hrel,hh,hclock⟩

/-- The explicit timeout label executes one final block to ordinary halt. This
does not by itself implement Boolean-output cleanup or distinguish the result
after the label has been erased. -/
theorem timeout_next (ks states symbols : Nat) (p : Program) (input output main initial : Nat)
    (c : (finiteCore ks states symbols p input output main initial).Cfg) :
    (clocked ks states symbols p input output main initial).step (timeoutCfg ks states symbols p.length c) =
      some ⟨none,(none,c.var),embedStacks ks symbols [] [] c.stk⟩ := by
  rfl

/-- Every validated numeric run reaches either an ordinary halt or the
explicit timeout label within `fuel + 1` clocked statement blocks. This proves
progress with a preloaded clock, not an input-driven clock initializer. -/
theorem validated_clock_progress (ks states symbols : Nat) (p : Program) (input output main initial fuel : Nat)
    (hp : programValid p ks states symbols = true) (start : Result)
    (hvalid : resultValid ks states symbols p.length start) :
    ∃ n ≤ fuel+1, ∃ c',
      runSteps (clocked ks states symbols p input output main initial).step n
        (embed ks states symbols p.length none (List.replicate fuel true)
          (finiteConfig ks states symbols p.length start)) = some c' ∧
      (c'.l = none ∨ c'.l = some (.inl false)) := by
  have hs := run_safe p ks states symbols hp fuel start hvalid
  cases hr : run p fuel start with
  | invalid =>
    rw [hr] at hs
    contradiction
  | timeout result =>
    obtain ⟨c',hrel,hclock⟩ := numeric_timeout ks states symbols p input output main initial fuel hp start result hvalid hr
    exact ⟨fuel+1,by omega,timeoutCfg ks states symbols p.length c',hclock,Or.inr rfl⟩
  | halted result =>
    obtain ⟨n,hn,c',flag',hrel,hh,hclock⟩ := numeric_halt ks states symbols p input output main initial fuel hp start result hvalid hr
    refine ⟨n,by omega,embed ks states symbols p.length flag' ((List.replicate fuel true).drop n) c',hclock,Or.inl ?_⟩
    simp [embed,embedCfg,hh,Option.map] <;> rfl

/-- The validated pair initializer supplies a valid core start; the clock
stack is still explicitly preloaded for this intermediate theorem. -/
theorem pair_clock_progress (d : Shared.ComplexityBridge.TM2BooleanInput.InputData) (p : Program)
    (output exponent : Nat) (x w : List Bool)
    (hdata : Shared.ComplexityBridge.TM2BooleanInput.validInputData d = true)
    (hmain : d.main < p.length) (hp : programValid p d.stackCount d.states d.symbols = true) :
    ∃ start, Shared.ComplexityBridge.TM2BooleanInput.buildStart d (BitstringEncoding.bitEncode (x,w)) = some start ∧
      ∃ n ≤ (x.length+w.length+2)^exponent+1, ∃ c',
        runSteps (clocked d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState).step n
          (embed d.stackCount d.states d.symbols p.length none
            (List.replicate ((x.length+w.length+2)^exponent) true)
            (finiteConfig d.stackCount d.states d.symbols p.length start)) = some c' ∧
        (c'.l = none ∨ c'.l = some (.inl false)) := by
  obtain ⟨start,hs,hvalid⟩ := Shared.ComplexityBridge.TM2FiniteBoundary.buildStart_valid d
    (BitstringEncoding.bitEncode (x,w)) p hdata hmain
  refine ⟨start,hs,?_⟩
  exact validated_clock_progress d.stackCount d.states d.symbols p d.inputStack output d.main d.initialState
    ((x.length+w.length+2)^exponent) hp start hvalid

/-- Zero ticks time out before the first core block. -/
example : (runSteps (clocked 0 1 1 [.halt] 0 0 0 0).step 1
    (embed 0 1 1 1 none [] (finiteConfig 0 1 1 1 ⟨some 0,0,[]⟩))).map (fun c => c.l) = some (some (.inl false)) := by
  change (Option.map (fun c => c.l) (runSteps (clocked 0 1 1 [.halt] 0 0 0 0).step 1
    (embed 0 1 1 1 none [] (finiteConfig 0 1 1 1 ⟨some 0,0,[]⟩))) : Option (Option (Bool ⊕ Fin 2))) = some (some (.inl false))
  decide

/-- One tick permits a one-block halt at the exact boundary. -/
example : (runSteps (clocked 0 1 1 [.halt] 0 0 0 0).step 1
    (embed 0 1 1 1 none [true] (finiteConfig 0 1 1 1 ⟨some 0,0,[]⟩))).map (fun c => c.l) = some none := by
  change (Option.map (fun c => c.l) (runSteps (clocked 0 1 1 [.halt] 0 0 0 0).step 1
    (embed 0 1 1 1 none [true] (finiteConfig 0 1 1 1 ⟨some 0,0,[]⟩))) : Option (Option (Bool ⊕ Fin 2))) = some none
  decide

end Shared.ComplexityBridge.TM2UnaryClock
