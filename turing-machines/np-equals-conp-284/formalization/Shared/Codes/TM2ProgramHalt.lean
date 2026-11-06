import Shared.Codes.TM2Program

/-! Converse bounded-halting correspondence for validated numeric TM2
programs. This is not yet a canonical FinTM2 coverage or bit-cost theorem. -/
namespace Shared.Codes.TM2Program
open Shared.Codes.TM2StatementExecution Shared.Codes.TM2StatementValidation
open Shared.ComplexityBridge.TM2Symbols

/-- Exact runs compose, with failure propagated after the first halted step. -/
theorem runSteps_add {α : Type} (f : α → Option α) (m n : Nat) (c : α) :
    runSteps f (m + n) c = (runSteps f m c).bind (runSteps f n) := by
  induction n with
  | zero => simp [runSteps]
  | succ n ih =>
    rw [Nat.add_succ]
    change (runSteps f (m + n) c).bind f =
      (runSteps f m c).bind (fun x => (runSteps f n x).bind f)
    rw [ih]
    cases h : runSteps f m c <;> rfl

/-- No successful exact run can extend beyond a configuration whose next step
is absent. -/
theorem runSteps_before_terminal {α : Type} (f : α → Option α) (c d e : α)
    (n m : Nat) (hn : runSteps f n c = some d) (hd : f d = none)
    (hm : runSteps f m c = some e) : m ≤ n := by
  by_contra h
  have hle : n + 1 ≤ m := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  have heq : m = n + (k + 1) := by omega
  rw [heq, runSteps_add, hn] at hm
  simp [runSteps_front, hd] at hm

/-- Validated bounded execution returns a halted result exactly when the
semantic numeric TM2 reaches that halted configuration within the fuel. -/
theorem validated_halt_iff (p : Program) (ks states symbols fuel : Nat)
    (hp : programValid p ks states symbols = true) (c : Result)
    (hc : resultValid ks states symbols p.length c)
    (target : Turing.TM2.Cfg (fun _ : Nat => Nat) Nat Nat)
    (htarget : target.l = none) :
    (∃ d, run p fuel c = .halted d ∧ erase d = target) ↔
      ∃ n ≤ fuel, runSteps (Turing.TM2.step (semanticProgram p)) n (erase c) = some target := by
  let f := Turing.TM2.step (semanticProgram p)
  have hterm : f target = none := by
    cases target with
    | mk lab state stk =>
      cases lab with
      | none => rfl
      | some l => cases htarget
  constructor
  · rintro ⟨d, hr, he⟩
    have href := run_refines p fuel c
    rw [hr] at href
    rcases href with ⟨n, hn, hrun, _⟩
    exact ⟨n, hn, by simpa [f, he] using hrun⟩
  · rintro ⟨n, hn, hreach⟩
    have hsafe := run_safe p ks states symbols hp fuel c hc
    have href := run_refines p fuel c
    cases hr : run p fuel c with
    | invalid => simp [hr, safeOutcome] at hsafe
    | timeout d =>
      have hrun : runSteps f fuel (erase c) = some (erase d) := by simpa [hr, outcomeRefines, f] using href
      have hbound := runSteps_before_terminal f (erase c) target (erase d) n fuel hreach hterm hrun
      have heq : fuel = n := by omega
      have hcfg : erase d = target := by
        rw [heq, hreach] at hrun
        exact Option.some.inj hrun.symm
      have hlabel : d.label = none := by
        have h := congrArg Turing.TM2.Cfg.l hcfg
        simpa [erase, htarget] using h
      have hsafe' : resultValid ks states symbols p.length d ∧ d.label ≠ none := by
        simpa [hr, safeOutcome] using hsafe
      have hne : d.label ≠ none := hsafe'.2
      exact False.elim (hne hlabel)
    | halted d =>
      have hh : ∃ k ≤ fuel, runSteps f k (erase c) = some (erase d) ∧ d.label = none := by
        simpa [hr, outcomeRefines, f] using href
      obtain ⟨k, hk, hrun, hdlabel⟩ := hh
      have hdterm : f (erase d) = none := by simp [f, erase, Turing.TM2.step, hdlabel]
      have hk_le := runSteps_before_terminal f (erase c) target (erase d) n k hreach hterm hrun
      have hn_le := runSteps_before_terminal f (erase c) (erase d) target k n hrun hdterm hreach
      have heq : k = n := by omega
      have hcfg : erase d = target := by
        rw [heq, hreach] at hrun
        exact Option.some.inj hrun.symm
      exact ⟨d, rfl, hcfg⟩

/-- The same equivalence stated with mathlib's timed evaluation structure. -/
theorem validated_halt_iff_evals (p : Program) (ks states symbols fuel : Nat)
    (hp : programValid p ks states symbols = true) (c : Result)
    (hc : resultValid ks states symbols p.length c)
    (target : Turing.TM2.Cfg (fun _ : Nat => Nat) Nat Nat)
    (htarget : target.l = none) :
    (∃ d, run p fuel c = .halted d ∧ erase d = target) ↔
      Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step (semanticProgram p))
        (erase c) (some target) fuel) := by
  rw [validated_halt_iff p ks states symbols fuel hp c hc target htarget]
  constructor
  · rintro ⟨n, hn, hr⟩
    refine ⟨⟨⟨n, ?_⟩, hn⟩⟩
    rw [runSteps_iterate] at hr
    change (fun o : Option (Turing.TM2.Cfg (fun _ : Nat => Nat) Nat Nat) =>
      o.bind (Turing.TM2.step (semanticProgram p)))^[n] (some (erase c)) = some target
    exact hr
  · rintro ⟨h⟩
    refine ⟨h.steps, h.steps_le_m, ?_⟩
    rw [runSteps_iterate]
    exact h.evals_in_steps

end Shared.Codes.TM2Program
