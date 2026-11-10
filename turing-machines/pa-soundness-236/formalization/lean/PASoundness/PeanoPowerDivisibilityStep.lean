import PASoundness.PeanoCommonMultiple
import PASoundness.PeanoPolynomialContext
import PASoundness.PeanoPolynomialQuotient

/-! Arithmetic steps used in a proposed induction on power divisibility. -/
namespace PASoundness.PeanoPowerDivisibilityStep
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication PeanoDivisibility
open PeanoCommonMultiple.DivisibilityBoundary

/-- PA preserves divisibility when a dividend is doubled. -/
theorem divides_double (k d : Peano.Term) : FormulaProves
    ((divides k d).imp (divides k (add d d))) := by
  have hpoly : FormulaProves ((mul d (add (succ zero) (succ zero))).equal (add d d)) := by
    apply PeanoPolynomialQuotient.cls_exact
    simp only [PeanoPolynomialQuotient.cls_add, PeanoPolynomialQuotient.cls_mul,
      PeanoPolynomialQuotient.cls_one]
    ring
  exact FOL.Derivation.compose (divides_mul k d (add (succ zero) (succ zero)))
    (.mp (dividend_congr k (mul d (add (succ zero) (succ zero))) (add d d)) hpoly)

/-- PA derives the divisibility boundary from the two displayed equalities.
This does not establish either equality or a power-trace hypothesis. -/
theorem boundary_of_equal (u r p : Peano.Term) : FormulaProves
    ((r.equal u).imp ((p.equal (add r r)).imp (divides (add u u) p))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Γ := [p.equal (add r r), r.equal u]
  have hr : FOL.Context Peano.Axiom Γ (r.equal u) := .hypothesis (by simp [Γ])
  have hp : FOL.Context Peano.Axiom Γ (p.equal (add r r)) := .head _ _
  have he : FOL.Context Peano.Axiom Γ ((add u u).equal p) := by
    apply PeanoPolynomialContext.cls_exact
    simp only [PeanoPolynomialContext.cls_add]
    have hru : PeanoPolynomialContext.cls Γ r = PeanoPolynomialContext.cls Γ u :=
      PeanoPolynomialContext.cls_sound hr
    have hpr : PeanoPolynomialContext.cls Γ p =
        PeanoPolynomialContext.cls Γ r + PeanoPolynomialContext.cls Γ r := by
      simpa only [PeanoPolynomialContext.cls_add] using PeanoPolynomialContext.cls_sound hp
    rw [hpr, hru]
  exact .mp (.mp (.closed (dividend_congr (add u u) (add u u) p)) he)
    (.closed (divides_self (add u u)))

end PASoundness.PeanoPowerDivisibilityStep

#print axioms PASoundness.PeanoPowerDivisibilityStep.divides_double
#print axioms PASoundness.PeanoPowerDivisibilityStep.boundary_of_equal
