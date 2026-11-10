import PASoundness.PeanoPowerExistenceBase
import PASoundness.PeanoBetaCRTPrefixSubst

/-! PA induction from the literal power-trace successor implication. The
successor derivation is an explicit premise; no semantic soundness is used. -/
namespace PASoundness.PeanoPowerTotality
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- A power trace exists at the free index named 0. -/
def existsPower : Peano.Formula := FOL.existsAt 6 (pow2 (.var 0) (.var 6))

/-- The exact base substitution through the existential output witness. -/
theorem base_syntax : FOL.substAt existsPower 0 zero =
    FOL.existsAt 6 (pow2 zero (.var 6)) := by
  rw [existsPower, PeanoBetaCRTPrefixSubst.Syntax.subst_zero_existsAt _ 0 6 (by decide)]
  simp [FOL.substAt, pow2_subst, FirstOrder.Language.Term.subst]

/-- The exact successor substitution preserves the existential output binder. -/
theorem successor_syntax : FOL.substAt existsPower 0 (succ (.var 0)) =
    FOL.existsAt 6 (pow2 (succ (.var 0)) (.var 6)) := by
  rw [existsPower, PeanoBetaCRTPrefixSubst.Syntax.subst_succSelf_existsAt _ 0 6 (by decide)]
  simp [FOL.substAt, pow2_subst, FirstOrder.Language.Term.subst]

/-- If PA proves the literal trace-successor implication, PA proves that
every natural number has a literal power trace. -/
theorem totality_of_successor
    (hstep : FormulaProves ((pow2 (.var 0) (.var 6)).imp
      (pow2 (succ (.var 0)) (add (.var 6) (.var 6))))) :
    FormulaProves (FOL.allAt 0 existsPower) := by
  let S := FOL.existsAt 6 (pow2 (succ (.var 0)) (.var 6))
  have hbase : FormulaProves (FOL.substAt existsPower 0 zero) := by
    rw [base_syntax]
    have hi := FOL.Derivation.existsIntro (A := Peano.Axiom) (pow2 zero (.var 6)) 6 (succ zero)
    have hs : FOL.substAt (pow2 zero (.var 6)) 6 (succ zero) = pow2 zero (succ zero) := by
      simp [FOL.substAt, pow2_subst, PeanoArithmetic.zero_subst, FirstOrder.Language.Term.subst]
    rw [hs] at hi
    exact .mp hi PeanoPowerExistenceBase.pow2_zero_one
  have hlocal : FormulaProves ((pow2 (.var 0) (.var 6)).imp S) := by
    have hi := FOL.Derivation.existsIntro (A := Peano.Axiom)
      (pow2 (succ (.var 0)) (.var 6)) 6 (add (.var 6) (.var 6))
    have hs : FOL.substAt (pow2 (succ (.var 0)) (.var 6)) 6
        (add (.var 6) (.var 6)) = pow2 (succ (.var 0)) (add (.var 6) (.var 6)) := by
      simp [FOL.substAt, pow2_subst, PeanoArithmetic.succ_subst,
        FirstOrder.Language.Term.subst]
    rw [hs] at hi
    exact FOL.Derivation.compose hstep hi
  have hfresh : 6 ∉ S.freeVarFinset := by
    simp [S, FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]
  have hsuccessor : FormulaProves (existsPower.imp (FOL.substAt existsPower 0 (succ (.var 0)))) := by
    rw [successor_syntax]
    exact PeanoBitPositionReduction.exists_elim 6 hfresh hlocal
  exact .mp (.mp (.axiom (.induction existsPower 0)) hbase) (.generalize 0 hsuccessor)

end PASoundness.PeanoPowerTotality

#print axioms PASoundness.PeanoPowerTotality.totality_of_successor
