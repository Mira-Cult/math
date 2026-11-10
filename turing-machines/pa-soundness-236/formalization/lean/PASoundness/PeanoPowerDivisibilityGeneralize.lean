import PASoundness.PeanoPowerDivisibilityInduction

/-! Generalization of a fixed-name successor body under the PA induction
family as context. -/
namespace PASoundness.PeanoPowerDivisibilityGeneralize
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoPowerDivisibilityInduction

/-- If PA derives the successor body under the induction-family hypothesis,
it derives the fully quantified successor family under the same hypothesis.
The hypothesis and the fixed-name body remain explicit. -/
theorem generalize_successor
    (h : FormulaProves (family.imp (body (succ (.var 0))))) :
    FormulaProves (family.imp (familyAt (succ (.var 0)))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  unfold familyAt
  apply FOL.Context.generalize 1
  · intro ψ hψ
    have he : ψ = family := by simpa using hψ
    subst ψ
    decide
  apply FOL.Context.generalize 2
  · intro ψ hψ
    have he : ψ = family := by simpa using hψ
    subst ψ
    decide
  apply FOL.Context.generalize 6
  · intro ψ hψ
    have he : ψ = family := by simpa using hψ
    subst ψ
    decide
  exact .mp (.closed h) (.head _ _)

end PASoundness.PeanoPowerDivisibilityGeneralize

#print axioms PASoundness.PeanoPowerDivisibilityGeneralize.generalize_successor
