import PASoundness.PeanoArithmetic
import PASoundness.FOLFreshEquality
/-! Object-level PA derivations involving successor and addition by one. -/
namespace PASoundness.PeanoArithmetic
open FirstOrder FirstOrder.Language
open Peano

/-- Equality is preserved by successor in the actual first-order calculus. -/
theorem succ_congruence (a b : Peano.Term) :
    FormulaProves ((a.equal b).imp ((succ a).equal (succ b))) := by
  obtain ⟨x, hx⟩ := FOL.fresh_for_term b
  let φ : Peano.Formula := (succ (.var x)).equal (succ b)
  have hb : FOL.substAt φ x b = (succ b).equal (succ b) := by
    simp only [FOL.substAt, φ, FOL.equality_subst, succ_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte]
    rw [FOL.term_subst_fresh b x b hx]
  have ha : FOL.substAt φ x a = (succ a).equal (succ b) := by
    simp only [FOL.substAt, φ, FOL.equality_subst, succ_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte]
    rw [FOL.term_subst_fresh b x a hx]
  have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
    (FOL.LogicalAxiom.eqSubst φ x b a)
  rw [hb, ha] at h
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hs : FOL.Context Peano.Axiom [a.equal b] (b.equal a) :=
    FOL.Context.eqSymm (FOL.Context.head [] (a.equal b))
  exact .mp (.mp (.closed h) hs) (.closed (.logical (.eqRefl _)))

/-- PA proves `t + 1 = S t` for every arithmetic term. -/
theorem add_one (t : Peano.Term) : FormulaProves ((add t (succ zero)).equal (succ t)) := by
  have h := FOL.Derivation.mp (succ_congruence (add t zero) t) (.axiom (.add_zero t))
  exact FOL.Derivation.eqTrans (.axiom (.add_succ t zero)) h
end PASoundness.PeanoArithmetic
