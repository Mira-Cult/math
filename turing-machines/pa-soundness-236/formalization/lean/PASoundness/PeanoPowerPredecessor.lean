import PASoundness.PeanoPowerTransition
import PASoundness.PeanoOrderTransitive

/-! Restriction of the literal bounded power trace inside genuine PA. -/
namespace PASoundness.PeanoPowerPredecessor
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoPowerTransition

/-- The actual transition body restricted to indices below variable 0. -/
def smallerBody : Peano.Formula :=
  (less (.var 4) (.var 0)).imp (transition (.var 2) (.var 3) (.var 4) 5 6)

def smallerTrace : Peano.Formula := FOL.allAt 4 smallerBody

/-- PA restricts the full `k<S n` trace to `k<n`, without a semantic bound. -/
theorem restrict_trace : FormulaProves ((FOL.allAt 4 boundedBody).imp smallerTrace) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  change FOL.Context Peano.Axiom [FOL.allAt 4 boundedBody] (FOL.allAt 4 smallerBody)
  apply FOL.Context.generalize 4
  · intro ψ hψ
    have he : ψ = FOL.allAt 4 boundedBody := by simpa only [List.mem_singleton] using hψ
    subst ψ
    simp [SyntaxTransport.allAt_freeVars]
  · change FOL.Context Peano.Axiom [FOL.allAt 4 boundedBody]
      ((less (.var 4) (.var 0)).imp (transition (.var 2) (.var 3) (.var 4) 5 6))
    apply FOL.Context.deduction
    have hlt : FOL.Context Peano.Axiom [less (.var 4) (.var 0), FOL.allAt 4 boundedBody]
        (less (.var 4) (.var 0)) := FOL.Context.head _ _
    have hlarge : FOL.Context Peano.Axiom [less (.var 4) (.var 0), FOL.allAt 4 boundedBody]
        (less (.var 4) (succ (.var 0))) :=
      .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all (.var 4) (.var 0) (succ (.var 0)))) hlt)
        (.closed (self_less_succ (.var 0)))
    have htrace : FOL.Context Peano.Axiom [less (.var 4) (.var 0), FOL.allAt 4 boundedBody]
        boundedBody := FOL.Context.allSelf (FOL.Context.under (FOL.Context.head [] _) _)
    exact .mp htrace hlarge

/-- The original source rows with the strict smaller-index trace. -/
def smallerPowerBody : Peano.Formula :=
  (beta (.var 2) (.var 3) zero (succ zero)) ⊓
    ((beta (.var 2) (.var 3) (.var 0) (.var 5)) ⊓ smallerTrace)

/-- An endpoint predecessor satisfying the genuine `pow2 n r` formula. -/
def predecessorPower : Peano.Formula := FOL.existsAt 5
  ((pow2 (.var 0) (.var 5)) ⊓
    ((.var 1 : Peano.Term).equal (add (.var 5) (.var 5))))

private theorem smaller_pow2_syntax : pow2 (.var 0) (.var 5) =
    FOL.existsAt 2 (FOL.existsAt 3 smallerPowerBody) := by
  simp [pow2, pow2Template, smallerPowerBody, smallerTrace, smallerBody, transition, transitionBody,
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
  all_goals
    congr 1
    funext i
    fin_cases i
    congr 1
    funext j
    fin_cases j
    · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
      congr 1
      funext k
      fin_cases k
      simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
      all_goals
        congr 1
        funext z
        exact Fin.elim0 z
    · simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]

private def priorRow : Peano.Formula :=
  (beta (.var 2) (.var 3) (.var 0) (.var 5)) ⊓
    ((.var 1 : Peano.Term).equal (add (.var 5) (.var 5)))

private theorem prior_row_repackage : FormulaProves
    (priorRow.imp (preservedBody.imp predecessorPower)) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hrow : FOL.Context Peano.Axiom [preservedBody, priorRow] priorRow :=
    FOL.Context.under (FOL.Context.head [] priorRow) preservedBody
  have hp : FOL.Context Peano.Axiom [preservedBody, priorRow] preservedBody := FOL.Context.head _ _
  have hzero : FOL.Context Peano.Axiom [preservedBody, priorRow]
      (beta (.var 2) (.var 3) zero (succ zero)) := FOL.Context.conjunctionLeft hp
  have hlarge : FOL.Context Peano.Axiom [preservedBody, priorRow] (FOL.allAt 4 boundedBody) :=
    FOL.Context.conjunctionRight (FOL.Context.conjunctionRight hp)
  have hsmall : FOL.Context Peano.Axiom [preservedBody, priorRow] smallerTrace :=
    .mp (.closed restrict_trace) hlarge
  have hprior : FOL.Context Peano.Axiom [preservedBody, priorRow]
      (beta (.var 2) (.var 3) (.var 0) (.var 5)) := FOL.Context.conjunctionLeft hrow
  have heq : FOL.Context Peano.Axiom [preservedBody, priorRow]
      ((.var 1 : Peano.Term).equal (add (.var 5) (.var 5))) := FOL.Context.conjunctionRight hrow
  have hbody : FOL.Context Peano.Axiom [preservedBody, priorRow] smallerPowerBody :=
    FOL.Context.conjunctionIntro hzero (FOL.Context.conjunctionIntro hprior hsmall)
  have intro₃ : FormulaProves (smallerPowerBody.imp (FOL.existsAt 3 smallerPowerBody)) := by
    simpa only [SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom) smallerPowerBody 3 (.var 3))
  have h₃ : FOL.Context Peano.Axiom [preservedBody, priorRow] (FOL.existsAt 3 smallerPowerBody) :=
    .mp (.closed intro₃) hbody
  have intro₂ : FormulaProves
      ((FOL.existsAt 3 smallerPowerBody).imp (FOL.existsAt 2 (FOL.existsAt 3 smallerPowerBody))) := by
    simpa only [SyntaxTransport.substAt_self] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom) (FOL.existsAt 3 smallerPowerBody) 2 (.var 2))
  have hpow : FOL.Context Peano.Axiom [preservedBody, priorRow] (pow2 (.var 0) (.var 5)) := by
    rw [smaller_pow2_syntax]
    exact .mp (.closed intro₂) h₃
  let output : Peano.Formula := (pow2 (.var 0) (.var 5)) ⊓
    ((.var 1 : Peano.Term).equal (add (.var 5) (.var 5)))
  have hout : FOL.Context Peano.Axiom [preservedBody, priorRow] output :=
    FOL.Context.conjunctionIntro hpow heq
  have intro₅ : FormulaProves (output.imp predecessorPower) := by
    simpa only [SyntaxTransport.substAt_self, predecessorPower, output] using
      (FOL.Derivation.existsIntro (A := Peano.Axiom) output 5 (.var 5))
  exact .mp (.closed intro₅) hout

private theorem preserved_repackage : FormulaProves (preservedBody.imp predecessorPower) := by
  have hfresh : 5 ∉ (preservedBody.imp predecessorPower).freeVarFinset := by decide
  have h₅ := PeanoBitPositionReduction.exists_elim 5 hfresh prior_row_repackage
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hp : FOL.Context Peano.Axiom [preservedBody] preservedBody := FOL.Context.head [] _
  have hprev : FOL.Context Peano.Axiom [preservedBody]
      (FOL.existsAt 5 priorRow) := FOL.Context.conjunctionLeft (FOL.Context.conjunctionRight hp)
  exact .mp (.mp (.closed h₅) hprev) hp

/-- Repackage the preserved literal beta code and restricted trace into an
actual `pow2 n r` predecessor with endpoint equality `p=r+r`. -/
theorem preserved_to_power : FormulaProves (positivePredecessor.imp predecessorPower) := by
  have hfresh3 : 3 ∉ predecessorPower.freeVarFinset := by decide
  have h₃ := PeanoBitPositionReduction.exists_elim 3 hfresh3 preserved_repackage
  have hfresh2 : 2 ∉ predecessorPower.freeVarFinset := by decide
  have h₂ := PeanoBitPositionReduction.exists_elim 2 hfresh2 h₃
  exact h₂

/-- Actual successor/predecessor relation for the specified beta-coded
power formula, proved inside PA with its existential predecessor explicit. -/
theorem power_successor_predecessor :
    FormulaProves ((pow2 (succ (.var 0)) (.var 1)).imp predecessorPower) :=
  FOL.Derivation.compose PeanoPowerTransition.power_successor_predecessor preserved_to_power

end PASoundness.PeanoPowerPredecessor
