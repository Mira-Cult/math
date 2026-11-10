import PASoundness.PeanoFiniteComprehensionSubst

/-! Conditional PA induction for bounded selector codes.

The successor derivation is an explicit metatheoretic premise. This module
does not establish that premise, global bit support, or the literal AX8 formula.
-/
namespace PASoundness.PeanoFiniteComprehensionInduction
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoFiniteComprehensionBase PeanoFiniteComprehensionSubst

/-- The actual PA induction axiom combines the proved empty-prefix base with
an explicitly supplied PA successor derivation. The relation may depend on
the index name 1 and on any parameter other than the three displayed fresh
state names. -/
theorem induction_of_step (φ : Peano.Formula)
    (hφ0 : 0 ∉ φ.freeVarFinset) (hφ2 : 2 ∉ φ.freeVarFinset)
    (hφ3 : 3 ∉ φ.freeVarFinset)
    (hstep : FormulaProves ((invariant φ (.var 0)).imp
      (invariant φ (succ (.var 0))))) :
    FormulaProves (FOL.allAt 0 (invariant φ (.var 0))) := by
  let I := invariant φ (.var 0)
  have hbase : FormulaProves (FOL.substAt I 0 zero) := by
    rw [invariant_zero φ hφ0]
    exact PeanoFiniteComprehensionBase.base φ hφ2 hφ3
  have hsuccessor : FormulaProves (I.imp (FOL.substAt I 0 (succ (.var 0)))) := by
    rw [invariant_succ φ hφ0]
    exact hstep
  exact .mp (.mp (.axiom (.induction I 0)) hbase) (.generalize 0 hsuccessor)

end PASoundness.PeanoFiniteComprehensionInduction

#print axioms PASoundness.PeanoFiniteComprehensionInduction.induction_of_step
