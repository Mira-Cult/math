import Mathlib.Computability.TuringMachine.ToPartrec
import Shared.PNP.TM2Candidate
import Shared.NPCONP.TM2Verifier
import Shared.Codes.TM2ProgramHalt

/-! Finite-support TM2 implementations for the two actual comparison
predicates. The program code is obtained from the constructive partial
recursive representation theorem; the TM2 interpreter is a fixed executable
finite-alphabet machine. This is a qualitative termination theorem, not a
binary-tape compiler, a time bound, or an event-refinement certificate. -/
namespace Shared.Beeping.ComparisonTM2

open Turing.ToPartrec Turing.PartrecToTM2

/-- A numerical, unambiguous Boolean result. -/
def result (R : Nat → Nat → Bool) (e n : Nat) : Nat := if R e n then 1 else 0

theorem result_computable (R : Nat → Nat → Bool) (hR : Computable₂ R) :
    Computable₂ (result R) := by
  have h := Computable.cond hR (Computable.const 1) (Computable.const 0)
  apply h.of_eq
  rintro ⟨e,n⟩
  simp only [result]
  cases R e n <;> rfl

/-- A single finite source program computes the comparison on all inputs.
Its source input is exactly `[e,n]`; its result is a singleton containing 0
or 1. Existence of the code is mathematical, not a runtime oracle. -/
theorem comparison_has_code (R : Nat → Nat → Bool) (hR : Computable₂ R) :
    ∃ c : Code, ∀ e n, c.eval [e,n] = pure [result R e n] := by
  have hp : Nat.Partrec' (fun v : List.Vector Nat 2 =>
      (pure (result R v.head v.tail.head) : Part Nat)) :=
    Nat.Partrec'.part_iff₂.mpr (result_computable R hR).partrec₂
  obtain ⟨c,hc⟩ := Code.exists_code hp
  refine ⟨c, ?_⟩
  intro e n
  have h := hc (⟨[e,n], rfl⟩ : List.Vector Nat 2)
  change c.eval [e,n] = pure [result R e n] at h
  exact h

/-- The same code runs to the exact cleaned halt configuration of the
four-stack, four-symbol TM2 interpreter for every candidate and test index.
`Reaches` is finite reflexive-transitive reachability. -/
theorem comparison_has_terminating_tm2 (R : Nat → Nat → Bool) (hR : Computable₂ R) :
    ∃ c : Code, ∀ e n,
      StateTransition.Reaches (Turing.TM2.step tr) (init c [e,n])
        (halt [result R e n]) ∧
      Turing.TM2.step tr (halt [result R e n]) = none := by
  obtain ⟨c,hc⟩ := comparison_has_code R hR
  refine ⟨c, ?_⟩
  intro e n
  apply StateTransition.mem_eval.mp
  rw [tr_eval, hc e n]
  change halt [result R e n] ∈ Part.some (halt [result R e n])
  exact Part.mem_some_iff.mpr rfl

/-- Finite reachability gives an exact finite transition count. -/
theorem reaches_runSteps {α : Type} {step : α → Option α} {a b : α}
    (h : StateTransition.Reaches step a b) :
    ∃ d, Shared.ComplexityBridge.TM2Symbols.runSteps step d a = some b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hs ih =>
    obtain ⟨d,hd⟩ := ih
    refine ⟨d+1, ?_⟩
    change (Shared.ComplexityBridge.TM2Symbols.runSteps step d _).bind step = _
    rw [hd]
    exact hs

/-- In addition to termination, the compiler exposes a positive segment
length for each comparison and a finite support for its program labels. -/
theorem comparison_has_positive_run (R : Nat → Nat → Bool) (hR : Computable₂ R) :
    ∃ c : Code,
      @Turing.TM2.Supports _ _ _ _ ⟨trNormal c Cont'.halt⟩ tr (codeSupp c Cont'.halt) ∧
      ∀ e n, ∃ d, 0 < d ∧
        Shared.ComplexityBridge.TM2Symbols.runSteps (Turing.TM2.step tr) d (init c [e,n]) =
          some (halt [result R e n]) := by
  obtain ⟨c,hc⟩ := comparison_has_terminating_tm2 R hR
  refine ⟨c, tr_supports c Cont'.halt, ?_⟩
  intro e n
  obtain ⟨d,hd⟩ := reaches_runSteps (hc e n).1
  refine ⟨d, ?_, hd⟩
  by_contra hn
  have hz : d = 0 := by omega
  subst d
  change some (init c [e,n]) = some (halt [result R e n]) at hd
  have he := Option.some.inj hd
  have hl := congrArg Turing.TM2.Cfg.l he
  simp [init, halt] at hl

/-- Each of the separately coded comparisons has its own finite evaluator. -/
theorem pnp_has_terminating_tm2 :
    ∃ c : Code, ∀ e n,
      StateTransition.Reaches (Turing.TM2.step tr) (init c [e,n])
        (halt [result Shared.PNP.TM2Candidate.compareSAT e n]) ∧
      Turing.TM2.step tr (halt [result Shared.PNP.TM2Candidate.compareSAT e n]) = none :=
  comparison_has_terminating_tm2 _ Shared.PNP.TM2Candidate.compareSAT_computable

theorem npconp_has_terminating_tm2 :
    ∃ c : Code, ∀ e n,
      StateTransition.Reaches (Turing.TM2.step tr) (init c [e,n])
        (halt [result Shared.NPCONP.TM2Verifier.compare e n]) ∧
      Turing.TM2.step tr (halt [result Shared.NPCONP.TM2Verifier.compare e n]) = none :=
  comparison_has_terminating_tm2 _ Shared.NPCONP.TM2Verifier.compare_computable

/-- Separate positive-duration evaluator for the P = NP candidate test. -/
theorem pnp_has_positive_run :
    ∃ c : Code,
      @Turing.TM2.Supports _ _ _ _ ⟨trNormal c Cont'.halt⟩ tr (codeSupp c Cont'.halt) ∧
      ∀ e n, ∃ d, 0 < d ∧
        Shared.ComplexityBridge.TM2Symbols.runSteps (Turing.TM2.step tr) d (init c [e,n]) =
          some (halt [result Shared.PNP.TM2Candidate.compareSAT e n]) :=
  comparison_has_positive_run _ Shared.PNP.TM2Candidate.compareSAT_computable

/-- Separate positive-duration evaluator for the NP = coNP candidate test. -/
theorem npconp_has_positive_run :
    ∃ c : Code,
      @Turing.TM2.Supports _ _ _ _ ⟨trNormal c Cont'.halt⟩ tr (codeSupp c Cont'.halt) ∧
      ∀ e n, ∃ d, 0 < d ∧
        Shared.ComplexityBridge.TM2Symbols.runSteps (Turing.TM2.step tr) d (init c [e,n]) =
          some (halt [result Shared.NPCONP.TM2Verifier.compare e n]) :=
  comparison_has_positive_run _ Shared.NPCONP.TM2Verifier.compare_computable

end Shared.Beeping.ComparisonTM2
