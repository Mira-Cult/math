import PASoundness.PeanoBetaProductIncrement

/-! Genuine PA proofs of right distributivity and associativity. -/
namespace PASoundness.PeanoMultiplicationAssociative
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication

/-- PA equality congruence in the second multiplication argument. -/
theorem mul_right_congr (t a b : Peano.Term) :
    FormulaProves ((a.equal b).imp ((mul t a).equal (mul t b))) := by
  obtain ⟨i, hi⟩ := FOL.fresh_for_term (add t a)
  have hi' : i ∉ t.varFinset ∧ i ∉ a.varFinset := by
    simpa [Peano.add, FirstOrder.Language.Term.varFinset] using hi
  let φ : Peano.Formula := (mul t a).equal (mul t (.var i))
  have h₀ : FOL.substAt φ i a = (mul t a).equal (mul t a) := by
    simp only [FOL.substAt, φ, FOL.equality_subst, mul_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh t i a hi'.1, FOL.term_subst_fresh a i a hi'.2]
  have h₁ : FOL.substAt φ i b = (mul t a).equal (mul t b) := by
    simp only [FOL.substAt, φ, FOL.equality_subst, mul_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh t i b hi'.1, FOL.term_subst_fresh a i b hi'.2]
  have h := FOL.Derivation.logical (Axiom := Peano.Axiom) (FOL.LogicalAxiom.eqSubst φ i a b)
  rw [h₀, h₁] at h
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  exact .mp (.mp (.closed h) (FOL.Context.head [] (a.equal b)))
    (.closed (.logical (.eqRefl _)))

/-- Right distributivity as a genuine PA derivation for arbitrary terms. -/
theorem mul_add_right (a b c : Peano.Term) :
    FormulaProves ((mul a (add b c)).equal (add (mul a b) (mul a c))) := by
  have h₁ := PeanoBetaProductIncrement.mul_comm a (add b c)
  have h₂ := PeanoQuotientGap.mul_add_left b c a
  have h₃ := FOL.Derivation.mp
    (PeanoAdditionAssociative.add_left_congr (mul c a) (mul b a) (mul a b))
    (PeanoBetaProductIncrement.mul_comm b a)
  have h₄ := FOL.Derivation.mp
    (PeanoAdditionAssociative.add_right_congr (mul a b) (mul c a) (mul a c))
    (PeanoBetaProductIncrement.mul_comm c a)
  exact FOL.Derivation.eqTrans (FOL.Derivation.eqTrans (FOL.Derivation.eqTrans h₁ h₂) h₃) h₄

/-- PA proves associativity of multiplication for arbitrary terms. The induction
variable is chosen fresh from both fixed factors. -/
theorem mul_assoc (a b c : Peano.Term) :
    FormulaProves ((mul (mul a b) c).equal (mul a (mul b c))) := by
  obtain ⟨i, hi⟩ := FOL.fresh_for_term (add a b)
  have hi' : i ∉ a.varFinset ∧ i ∉ b.varFinset := by
    simpa [Peano.add, FirstOrder.Language.Term.varFinset] using hi
  let w : Peano.Term := .var i
  let φ : Peano.Formula := (mul (mul a b) w).equal (mul a (mul b w))
  have hbase : FormulaProves (FOL.substAt φ i zero) := by
    have h₁ := FOL.Derivation.axiom (Peano.Axiom.mul_zero (mul a b))
    have h₂ := FOL.Derivation.mp (mul_right_congr a (mul b zero) zero)
      (.axiom (.mul_zero b))
    have h₃ := FOL.Derivation.axiom (Peano.Axiom.mul_zero a)
    have h := FOL.Derivation.eqTrans h₁ (FOL.Derivation.eqSymm (FOL.Derivation.eqTrans h₂ h₃))
    simpa only [FOL.substAt, φ, w, FOL.equality_subst, mul_subst, PeanoArithmetic.zero_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh a i zero hi'.1, FOL.term_subst_fresh b i zero hi'.2] using h
  have hstep : FormulaProves (φ.imp (FOL.substAt φ i (succ w))) := by
    have h : FormulaProves
        (φ.imp ((mul (mul a b) (succ w)).equal (mul a (mul b (succ w))))) := by
      apply FOL.Context.closeEmpty
      apply FOL.Context.deduction
      have h₁ := FOL.Derivation.axiom (Peano.Axiom.mul_succ (mul a b) w)
      have h₂ : FOL.Context Peano.Axiom [φ]
          ((add (mul (mul a b) w) (mul a b)).equal (add (mul a (mul b w)) (mul a b))) :=
        .mp (.closed (PeanoAdditionAssociative.add_left_congr (mul a b) _ _))
          (FOL.Context.head [] φ)
      have h₃ := FOL.Derivation.eqSymm (mul_add_right a (mul b w) b)
      have h₄ := FOL.Derivation.mp (mul_right_congr a (add (mul b w) b) (mul b (succ w)))
        (FOL.Derivation.eqSymm (.axiom (.mul_succ b w)))
      exact FOL.Context.eqTrans (FOL.Context.eqTrans (FOL.Context.eqTrans
        (.closed h₁) h₂) (.closed h₃)) (.closed h₄)
    simpa only [FOL.substAt, φ, w, FOL.equality_subst, mul_subst, succ_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh a i (succ (.var i)) hi'.1,
      FOL.term_subst_fresh b i (succ (.var i)) hi'.2] using h
  have hall : FormulaProves (FOL.allAt i φ) :=
    .mp (.mp (.axiom (.induction φ i)) hbase) (.generalize i hstep)
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim φ i c)) hall
  simpa only [FOL.substAt, φ, w, FOL.equality_subst, mul_subst,
    FirstOrder.Language.Term.subst, ↓reduceIte,
    FOL.term_subst_fresh a i c hi'.1, FOL.term_subst_fresh b i c hi'.2] using h

end PASoundness.PeanoMultiplicationAssociative
