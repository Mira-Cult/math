import PASoundness.PeanoPowerDivisibilityBase
import PASoundness.PeanoPowerDivisibilityGeneralize

/-! Assemble the PA divisibility induction from its explicit successor case. -/
namespace PASoundness.PeanoPowerDivisibilityCompose
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoPowerDivisibilityInduction

/-- The proved zero case and an explicit PA derivation of the open successor
case yield the universally quantified family by PA induction. -/
theorem family_of_open_successor
    (h : FormulaProves (family.imp (body (succ (.var 0))))) :
    FormulaProves (FOL.allAt 0 family) := by
  have hb : FormulaProves (familyAt zero) := by
    simpa only [familyAt, body, PeanoPowerDivisibilityBase.divisible] using
      PeanoPowerDivisibilityBase.zero_case_quantified
  exact family_of_base_and_step hb
    (PeanoPowerDivisibilityGeneralize.generalize_successor h)

/-- The same proof, with the quantified variables instantiated at their
fixed free names, supplies the open power-divisibility implication. -/
theorem body_of_open_successor
    (h : FormulaProves (family.imp (body (succ (.var 0))))) :
    FormulaProves (body (.var 0)) := by
  have hb : FormulaProves (familyAt zero) := by
    simpa only [familyAt, body, PeanoPowerDivisibilityBase.divisible] using
      PeanoPowerDivisibilityBase.zero_case_quantified
  exact body_of_base_and_step hb
    (PeanoPowerDivisibilityGeneralize.generalize_successor h)

end PASoundness.PeanoPowerDivisibilityCompose

#print axioms PASoundness.PeanoPowerDivisibilityCompose.family_of_open_successor
#print axioms PASoundness.PeanoPowerDivisibilityCompose.body_of_open_successor
