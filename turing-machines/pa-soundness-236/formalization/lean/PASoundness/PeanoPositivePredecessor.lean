import PASoundness.PeanoBitPositionReduction
import PASoundness.PeanoArithmetic

/-! Positive terms have predecessor witnesses in the literal PA calculus. -/
namespace PASoundness.PeanoPositivePredecessor
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- Capture-safe positive-predecessor formula. -/
def predecessorTemplate : Peano.Formula :=
  FOL.existsAt 1 ((.var 0 : Peano.Term).equal (succ (.var 1)))

def hasPredecessor (q : Peano.Term) : Peano.Formula :=
  predecessorTemplate.subst (fun x => if x = 0 then q else zero)

private theorem template_free : predecessorTemplate.freeVarFinset = {0} := by decide

theorem pred_variable : hasPredecessor (.var 0) = predecessorTemplate := by
  unfold hasPredecessor
  calc
    predecessorTemplate.subst (fun x => if x = 0 then .var 0 else zero) =
        predecessorTemplate.subst Term.var := by
      apply SyntaxTransport.formula_subst_agree
      intro y hy
      simp only [template_free, Finset.mem_singleton] at hy
      subst y
      rfl
    _ = predecessorTemplate := SyntaxTransport.formula_subst_var _

private theorem positive_variable : less zero (.var 0) =
    FOL.existsAt 5 ((add zero (succ (.var 5))).equal (.var 0)) := by
  simp [less, lessTemplate, exAt, v, FOL.existsAt, FOL.allAt, Peano.add, Peano.succ,
    Peano.zero, FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

theorem pred_subst (q : Peano.Term) (σ : Nat → Peano.Term) :
    (hasPredecessor q).subst σ = hasPredecessor (q.subst σ) := by
  unfold hasPredecessor
  rw [SyntaxTransport.formula_subst_comp]
  congr 1
  funext y
  by_cases h : y = 0 <;> simp [h]

private theorem positive_row : FormulaProves
    (((add zero (succ (.var 5))).equal (.var 0)).imp (hasPredecessor (.var 0))) := by
  rw [pred_variable]
  let body : Peano.Formula := (.var 0 : Peano.Term).equal (succ (.var 1))
  let row : Peano.Formula := (add zero (succ (.var 5))).equal (.var 0)
  have hs : FOL.substAt body 1 (.var 5) =
      ((.var 0 : Peano.Term).equal (succ (.var 5))) := by
    simp [FOL.substAt, body, FOL.equality_subst, succ_subst, FirstOrder.Language.Term.subst]
  have hIntro := FOL.Derivation.existsIntro (A := Peano.Axiom) body 1 (.var 5)
  rw [hs] at hIntro
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom [row] ((.var 0 : Peano.Term).equal (succ (.var 5))) :=
    FOL.Context.eqTrans (FOL.Context.eqSymm (FOL.Context.head [] row))
      (.closed (zero_add (succ (.var 5))))
  exact .mp (.closed hIntro) he

private theorem positive_variable_predecessor :
    FormulaProves ((less zero (.var 0)).imp (hasPredecessor (.var 0))) := by
  have hf : 5 ∉ (hasPredecessor (.var 0)).freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 5 hf positive_row
  simpa only [positive_variable] using h

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

/-- PA derives a predecessor witness from positivity, capture-safely for
arbitrary terms. This does not use metatheoretic arithmetic soundness. -/
theorem positive_has_predecessor (q : Peano.Term) :
    FormulaProves ((less zero q).imp (hasPredecessor q)) := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (.allElim ((less zero (.var 0)).imp (hasPredecessor (.var 0))) 0 q))
    (.generalize 0 positive_variable_predecessor)
  simpa only [FOL.substAt, subst_imp, less_subst, pred_subst,
    PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst, ↓reduceIte] using h

end PASoundness.PeanoPositivePredecessor
