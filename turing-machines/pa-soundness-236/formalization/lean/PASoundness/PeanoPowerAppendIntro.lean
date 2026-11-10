import PASoundness.PeanoPowerTransition

/-! Packaging a supplied literal doubling trace into the PA power formula.
No trace construction or power-totality theorem is asserted here. -/
namespace PASoundness.PeanoPowerAppendIntro
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- The new code is name 9, its parameter name 1, n name 0, and p name 6.
The transition binders are the distinct names 2, 3, and 4. -/
def traceMatrix : Peano.Formula :=
  beta (.var 9) (.var 1) zero (succ zero) ⊓
    (beta (.var 9) (.var 1) (succ (.var 0)) (add (.var 6) (.var 6)) ⊓
      FOL.allAt 2 ((less (.var 2) (succ (.var 0))).imp
        (FOL.existsAt 3 (FOL.existsAt 4
          (beta (.var 9) (.var 1) (.var 2) (.var 3) ⊓
            (beta (.var 9) (.var 1) (succ (.var 2)) (.var 4) ⊓
              ((.var 4 : Peano.Term).equal (add (.var 3) (.var 3)))))))))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem literal_syntax : pow2 (succ (.var 0)) (add (.var 6) (.var 6)) =
    FOL.existsAt 9 (FOL.existsAt 1 traceMatrix) := by
  simp [pow2, pow2Template, traceMatrix,
    FOL.existsAt, FOL.allAt, beta, betaTemplate, less, lessTemplate, modulus, exAt, v,
    Peano.add, Peano.mul, Peano.succ, Peano.zero, FirstOrder.Language.Term.equal,
    FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux, Min.min]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])
  all_goals try simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
  all_goals try
    (congr 1; funext i; fin_cases i; congr 1; funext j; fin_cases j <;>
      dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst] <;>
      first | rfl | (congr 1; funext k; fin_cases k; rfl))
  all_goals try (congr 1; funext i; exact Fin.elim0 i)
  all_goals try (congr 1; funext i; fin_cases i)
  all_goals try simp [FirstOrder.Language.Term.relabel]
  all_goals try (congr 1; funext i; fin_cases i)
  all_goals try simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst, Fin.elim0]
  all_goals try (congr 1; funext i; fin_cases i)
  all_goals try (congr 1; funext i; fin_cases i)

/-- Package the supplied code and parameter under their own binders. -/
theorem package_trace : FormulaProves
    (traceMatrix.imp (FOL.existsAt 9 (FOL.existsAt 1 traceMatrix))) := by
  have hi1 : FormulaProves (traceMatrix.imp (FOL.existsAt 1 traceMatrix)) := by
    simpa only [SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom) traceMatrix 1 (.var 1))
  have hi9 : FormulaProves ((FOL.existsAt 1 traceMatrix).imp
      (FOL.existsAt 9 (FOL.existsAt 1 traceMatrix))) := by
    simpa only [SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom) (FOL.existsAt 1 traceMatrix) 9 (.var 9))
  exact FOL.Derivation.compose hi1 hi9

/-- If PA has the displayed literal trace for the supplied B and C, it has
the literal power formula, with that same B and C as existential witnesses. -/
theorem trace_to_power : FormulaProves
    (traceMatrix.imp (pow2 (succ (.var 0)) (add (.var 6) (.var 6)))) := by
  rw [literal_syntax]
  exact package_trace

end PASoundness.PeanoPowerAppendIntro

#print axioms PASoundness.PeanoPowerAppendIntro.literal_syntax
#print axioms PASoundness.PeanoPowerAppendIntro.trace_to_power
