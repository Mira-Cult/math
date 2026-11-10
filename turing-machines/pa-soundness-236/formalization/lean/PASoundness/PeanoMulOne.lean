import PASoundness.PeanoMultiplication
import PASoundness.FOLFreshEquality
/-! A further object-level PA multiplication law. -/
namespace PASoundness.PeanoMultiplication
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic

/-- PA proves multiplication by one for an arbitrary arithmetic term. -/
theorem mul_one (t : Peano.Term) : FormulaProves ((mul t (succ zero)).equal t) := by
  obtain ⟨x, hx⟩ := FOL.fresh_for_term t
  let φ : Peano.Formula := (add (.var x) t).equal (add zero t)
  have h₀ : FOL.substAt φ x zero = (add zero t).equal (add zero t) := by
    simp only [FOL.substAt, φ, FOL.equality_subst, add_subst, zero_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte]
    rw [FOL.term_subst_fresh t x zero hx]
  have h₁ : FOL.substAt φ x (mul t zero) = (add (mul t zero) t).equal (add zero t) := by
    simp only [FOL.substAt, φ, FOL.equality_subst, add_subst, zero_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte]
    rw [FOL.term_subst_fresh t x (mul t zero) hx]
  have congruence : FormulaProves ((add (mul t zero) t).equal (add zero t)) := by
    have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
      (FOL.LogicalAxiom.eqSubst φ x zero (mul t zero))
    rw [h₀, h₁] at h
    exact .mp (.mp h (FOL.Derivation.eqSymm (.axiom (.mul_zero t)))) (.logical (.eqRefl _))
  exact FOL.Derivation.eqTrans
    (FOL.Derivation.eqTrans (.axiom (.mul_succ t zero)) congruence) (zero_add t)
end PASoundness.PeanoMultiplication
