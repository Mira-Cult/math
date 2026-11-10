import PASoundness.PeanoPowerUnique
import PASoundness.PeanoCommonMultiple
import PASoundness.PeanoPolynomialContext

/-! The equal-index branch of power divisibility, as an object-level PA proof. -/
namespace PASoundness.PeanoPowerDivisibilityBoundary
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic PeanoDivisibility
open PeanoCommonMultiple.DivisibilityBoundary

/-- Equality of indices transports a literal power trace within PA. -/
theorem power_index_congr (i n u : Peano.Term) : FormulaProves
    ((i.equal n).imp ((pow2 i u).imp (pow2 n u))) := by
  obtain ⟨j, hj⟩ := FOL.fresh_for_term u
  let φ := pow2 (.var j) u
  have h₀ : FOL.substAt φ j i = pow2 i u := by
    simp only [FOL.substAt, φ, pow2_subst, FirstOrder.Language.Term.subst,
      ↓reduceIte, FOL.term_subst_fresh u j i hj]
  have h₁ : FOL.substAt φ j n = pow2 n u := by
    simp only [FOL.substAt, φ, pow2_subst, FirstOrder.Language.Term.subst,
      ↓reduceIte, FOL.term_subst_fresh u j n hj]
  have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
    (FOL.LogicalAxiom.eqSubst φ j i n)
  rw [h₀, h₁] at h
  exact h

/-- At equal indices, uniqueness of power traces and the displayed successor
equation imply divisibility by the doubled lower power. -/
theorem equal_index_divides (i n u r p : Peano.Term) : FormulaProves
    ((i.equal n).imp ((pow2 i u).imp ((pow2 n r).imp
      ((p.equal (add r r)).imp (divides (add u u) p))))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Γ := [p.equal (add r r), pow2 n r, pow2 i u, i.equal n]
  have hi : FOL.Context Peano.Axiom Γ (i.equal n) := .hypothesis (by simp [Γ])
  have hu : FOL.Context Peano.Axiom Γ (pow2 i u) := .hypothesis (by simp [Γ])
  have hr : FOL.Context Peano.Axiom Γ (pow2 n r) := .hypothesis (by simp [Γ])
  have hp : FOL.Context Peano.Axiom Γ (p.equal (add r r)) := .head _ _
  have hnu : FOL.Context Peano.Axiom Γ (pow2 n u) :=
    .mp (.mp (.closed (power_index_congr i n u)) hi) hu
  have heq : FOL.Context Peano.Axiom Γ (r.equal u) :=
    .mp (.mp (.closed (PeanoPowerUnique.power_unique n r u)) hr) hnu
  have he : FOL.Context Peano.Axiom Γ ((add u u).equal p) := by
    apply PeanoPolynomialContext.cls_exact
    simp only [PeanoPolynomialContext.cls_add]
    have hru : PeanoPolynomialContext.cls Γ r = PeanoPolynomialContext.cls Γ u :=
      PeanoPolynomialContext.cls_sound heq
    have hpr : PeanoPolynomialContext.cls Γ p =
        PeanoPolynomialContext.cls Γ r + PeanoPolynomialContext.cls Γ r := by
      simpa only [PeanoPolynomialContext.cls_add] using PeanoPolynomialContext.cls_sound hp
    rw [hpr, hru]
  exact .mp (.mp (.closed (dividend_congr (add u u) (add u u) p)) he)
    (.closed (divides_self (add u u)))

end PASoundness.PeanoPowerDivisibilityBoundary

#print axioms PASoundness.PeanoPowerDivisibilityBoundary.power_index_congr
#print axioms PASoundness.PeanoPowerDivisibilityBoundary.equal_index_divides
