import Shared.Codes.TM2StatementValidation

/-! Bounded runs of finite numeric TM2 program tables. The exact count is in
mathlib statement blocks, not bit operations. `TM2Primcodable` proves computability of whole-program decoding; bit-cost
bounds and finite-beeper compilation remain open. -/
namespace Shared.Codes.TM2Program
open Shared.Codes.TM2Statements Shared.Codes.TM2StatementExecution Shared.Codes.TM2StatementValidation

abbrev Program := List Code

/-- Program enumeration uses the shared statement encoding. Its primitive
recursiveness is proved in `TM2Primcodable`. -/
def decodeProgram (e : Nat) : Option Program := Encodable.decode e

theorem decodeProgram_coverage (p : Program) :
    decodeProgram (Encodable.encode p) = some p := Encodable.encodek p

def programValid (p : Program) (ks states symbols : Nat) : Bool :=
  p.all (valid ks states symbols p.length)

def semanticProgram (p : Program) (l : Nat) : Turing.TM2.Stmt (fun _ : Nat => Nat) Nat Nat :=
  interpret ((p[l]?).getD .halt)

/-- A status distinguishes invalid program execution, an exhausted clock,
and a genuine halted configuration. -/
inductive Outcome where
  | invalid
  | timeout (config : Result)
  | halted (config : Result)
  deriving DecidableEq, Repr

/-- One unit of fuel executes one complete TM2 statement block. -/
def run (p : Program) : Nat → Result → Outcome
  | 0, c => if c.label.isNone then .halted c else .timeout c
  | n + 1, c =>
    match c.label with
    | none => .halted c
    | some l =>
      match p[l]? with
      | none => .invalid
      | some q =>
        match exec q c.state c.memory with
        | none => .invalid
        | some d => run p n d

def safeOutcome (ks states symbols labels : Nat) : Outcome → Prop
  | .invalid => False
  | .timeout c => resultValid ks states symbols labels c ∧ c.label ≠ none
  | .halted c => resultValid ks states symbols labels c ∧ c.label = none

theorem lookup_valid {p : Program} {ks states symbols l : Nat}
    (hp : programValid p ks states symbols = true) (hl : l < p.length) :
    ∃ q, p[l]? = some q ∧ valid ks states symbols p.length q = true := by
  let q := p[l]
  have hq : q ∈ p := List.getElem_mem hl
  refine ⟨q, ?_, ?_⟩
  · simp [q, hl]
  · exact (List.all_eq_true.mp hp) q hq

/-- Validated programs never fail a lookup or execution at any fuel limit. -/
theorem run_safe (p : Program) (ks states symbols : Nat)
    (hp : programValid p ks states symbols = true)
    (fuel : Nat) (c : Result) (hc : resultValid ks states symbols p.length c) :
    safeOutcome ks states symbols p.length (run p fuel c) := by
  induction fuel generalizing c with
  | zero =>
    cases hl : c.label with
    | none => simpa [run, hl, safeOutcome] using hc
    | some l => simp [run, hl, safeOutcome, hc]
  | succ n ih =>
    cases hl : c.label with
    | none => simpa [run, hl, safeOutcome] using hc
    | some l =>
      have hlt : l < p.length := hc.2.2 l hl
      obtain ⟨q, hq, hvalid⟩ := lookup_valid hp hlt
      obtain ⟨d, hd, hdvalid⟩ := exec_complete q ks states symbols p.length hvalid c.state c.memory hc.1 hc.2.1
      simpa [run, hl, hq, hd] using ih d hdvalid

/-- A successful numeric block agrees with one semantic TM2 step. -/
theorem step_sound (p : Program) (c d : Result) (l : Nat) (q : Code)
    (hl : c.label = some l) (hq : p[l]? = some q) (he : exec q c.state c.memory = some d) :
    Turing.TM2.step (semanticProgram p) (erase c) = some (erase d) := by
  simp only [erase, Turing.TM2.step, hl, semanticProgram, hq, Option.getD_some]
  exact congrArg some (exec_sound q c.state c.memory d he)

example : run [.halt] 0 ⟨some 0, 0, []⟩ = .timeout ⟨some 0, 0, []⟩ := by decide
example : run [.halt] 1 ⟨some 0, 0, []⟩ = .halted ⟨none, 0, []⟩ := by decide
example : run [] 1 ⟨some 0, 0, []⟩ = .invalid := by decide
example : run [] 0 ⟨none, 0, []⟩ = .halted ⟨none, 0, []⟩ := by decide
example : run [.goto [0]] 3 ⟨some 0, 0, []⟩ = .timeout ⟨some 0, 0, []⟩ := by decide
example : run [.goto []] 1 ⟨some 0, 0, []⟩ = .invalid := by decide

open Shared.ComplexityBridge.TM2Symbols

theorem runSteps_front {α : Type} (f : α → Option α) (n : Nat) (c : α) :
    runSteps f (n + 1) c = (f c).bind (runSteps f n) := by
  induction n generalizing c with
  | zero => simp [runSteps]
  | succ n ih =>
    change (runSteps f (n + 1) c).bind f = (f c).bind (fun d => (runSteps f n d).bind f)
    rw [ih c]
    cases hf : f c <;> rfl

def outcomeRefines (p : Program) (fuel : Nat) (c : Result) : Outcome → Prop
  | .invalid => True
  | .timeout d => runSteps (Turing.TM2.step (semanticProgram p)) fuel (erase c) = some (erase d)
  | .halted d => ∃ n ≤ fuel, runSteps (Turing.TM2.step (semanticProgram p)) n (erase c) = some (erase d) ∧ d.label = none

theorem outcomeRefines_step (p : Program) (n : Nat) (c d : Result) (out : Outcome)
    (hs : Turing.TM2.step (semanticProgram p) (erase c) = some (erase d))
    (h : outcomeRefines p n d out) : outcomeRefines p (n + 1) c out := by
  cases out with
  | invalid => trivial
  | timeout r =>
    change runSteps (Turing.TM2.step (semanticProgram p)) (n + 1) (erase c) = some (erase r)
    rw [runSteps_front, hs]
    exact h
  | halted r =>
    obtain ⟨k, hk, hkstep, hlabel⟩ := h
    refine ⟨k + 1, by omega, ?_, hlabel⟩
    rw [runSteps_front, hs]
    exact hkstep

/-- Finite execution follows the semantic TM2 run with the same number of
statement-block steps; halted outcomes may occur before the fuel is spent. -/
theorem run_refines (p : Program) (fuel : Nat) (c : Result) :
    outcomeRefines p fuel c (run p fuel c) := by
  induction fuel generalizing c with
  | zero =>
    cases hl : c.label with
    | none => simp [run, hl, outcomeRefines, runSteps]
    | some l => simp [run, hl, outcomeRefines, runSteps]
  | succ n ih =>
    cases hl : c.label with
    | none =>
      simp only [run, hl, outcomeRefines]
      exact ⟨0, Nat.zero_le _, rfl, trivial⟩
    | some l =>
      cases hq : p[l]? with
      | none => simp [run, hl, hq, outcomeRefines]
      | some q =>
        cases he : exec q c.state c.memory with
        | none => simp [run, hl, hq, he, outcomeRefines]
        | some d =>
          have hh := outcomeRefines_step p n c d (run p n d) (step_sound p c d l q hl hq he) (ih d)
          simpa [run, hl, hq, he] using hh

/-- The checked run cannot become invalid and follows the semantic run. -/
theorem validated_run_correct (p : Program) (ks states symbols fuel : Nat)
    (hp : programValid p ks states symbols = true) (c : Result)
    (hc : resultValid ks states symbols p.length c) :
    safeOutcome ks states symbols p.length (run p fuel c) ∧
      outcomeRefines p fuel c (run p fuel c) :=
  ⟨run_safe p ks states symbols hp fuel c hc, run_refines p fuel c⟩

end Shared.Codes.TM2Program
