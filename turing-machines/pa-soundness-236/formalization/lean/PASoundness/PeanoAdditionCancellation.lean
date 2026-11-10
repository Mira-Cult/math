import PASoundness.PeanoAdditionAssociative
import PASoundness.PeanoMultiplication

/-! PA cancellation and an equal-quotient remainder-uniqueness component.
Different quotient values remain outside this lemma. -/
namespace PASoundness.PeanoAdditionCancellation
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoAdditionAssociative

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

/-- For arbitrary arithmetic terms, PA proves cancellation of a common left
addend. The induction variable is fresh for both remaining terms. -/
theorem add_left_cancel (a b c : Peano.Term) :
    FormulaProves (((add a b).equal (add a c)).imp (b.equal c)) := by
  obtain ⟨i, hi⟩ := FOL.fresh_for_term (add b c)
  have hi' : i ∉ b.varFinset ∧ i ∉ c.varFinset := by
    simpa [Peano.add, FirstOrder.Language.Term.varFinset] using hi
  let w : Peano.Term := .var i
  let φ : Peano.Formula := ((add w b).equal (add w c)).imp (b.equal c)
  have hbase : FormulaProves (FOL.substAt φ i zero) := by
    have hh : FormulaProves (((add zero b).equal (add zero c)).imp (b.equal c)) := by
      apply FOL.Context.closeEmpty
      apply FOL.Context.deduction
      exact FOL.Context.eqTrans
        (FOL.Context.eqTrans (.closed (FOL.Derivation.eqSymm (zero_add b)))
          (FOL.Context.head [] ((add zero b).equal (add zero c))))
        (.closed (zero_add c))
    simpa only [FOL.substAt, φ, w, subst_imp, FOL.equality_subst, add_subst,
      zero_subst, FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh b i zero hi'.1, FOL.term_subst_fresh c i zero hi'.2] using hh
  have hstep : FormulaProves (φ.imp (FOL.substAt φ i (succ w))) := by
    have hh : FormulaProves (φ.imp
        (((add (succ w) b).equal (add (succ w) c)).imp (b.equal c))) := by
      apply FOL.Context.closeEmpty
      apply FOL.Context.deduction
      apply FOL.Context.deduction
      have heq : FOL.Context Peano.Axiom
          [((add (succ w) b).equal (add (succ w) c)), φ]
          ((succ (add w b)).equal (succ (add w c))) :=
        FOL.Context.eqTrans
          (FOL.Context.eqTrans (.closed (FOL.Derivation.eqSymm (add_succ_left w b)))
            (FOL.Context.head _ _))
          (.closed (add_succ_left w c))
      have heq' : FOL.Context Peano.Axiom
          [((add (succ w) b).equal (add (succ w) c)), φ]
          ((add w b).equal (add w c)) :=
        .mp (.closed (.axiom (.succ_injective (add w b) (add w c)))) heq
      exact .mp (FOL.Context.under (FOL.Context.head [] φ) _) heq'
    simpa only [FOL.substAt, φ, w, subst_imp, FOL.equality_subst, add_subst, succ_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh b i (succ (.var i)) hi'.1,
      FOL.term_subst_fresh c i (succ (.var i)) hi'.2] using hh
  have hall : FormulaProves (FOL.allAt i φ) :=
    .mp (.mp (.axiom (.induction φ i)) hbase) (.generalize i hstep)
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim φ i a)) hall
  simpa only [FOL.substAt, φ, w, subst_imp, FOL.equality_subst, add_subst,
    FirstOrder.Language.Term.subst, ↓reduceIte,
    FOL.term_subst_fresh b i a hi'.1, FOL.term_subst_fresh c i a hi'.2] using h

/-- Equal quotient terms and equal dividends force equal remainder terms.
No remainder bounds or semantic assumptions are used. -/
theorem equal_quotient_remainders (dividend quotient modulus r s : Peano.Term) :
    FormulaProves
      ((dividend.equal (add (mul quotient modulus) r)).imp
        ((dividend.equal (add (mul quotient modulus) s)).imp (r.equal s))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have e1 : FOL.Context Peano.Axiom
      [dividend.equal (add (mul quotient modulus) s),
        dividend.equal (add (mul quotient modulus) r)]
      ((add (mul quotient modulus) r).equal (add (mul quotient modulus) s)) :=
    FOL.Context.eqTrans
      (FOL.Context.eqSymm (FOL.Context.under (FOL.Context.head [] _) _))
      (FOL.Context.head _ _)
  exact .mp (.closed (add_left_cancel (mul quotient modulus) r s)) e1

/-- PA equality congruence for the first argument of multiplication. -/
theorem mul_left_congr (q q' m : Peano.Term) :
    FormulaProves ((q.equal q').imp ((mul q m).equal (mul q' m))) := by
  obtain ⟨i, hi⟩ := FOL.fresh_for_term (add q m)
  have hi' : i ∉ q.varFinset ∧ i ∉ m.varFinset := by
    simpa [Peano.add, FirstOrder.Language.Term.varFinset] using hi
  let φ : Peano.Formula := (mul q m).equal (mul (.var i) m)
  have h₀ : FOL.substAt φ i q = (mul q m).equal (mul q m) := by
    simp only [FOL.substAt, φ, FOL.equality_subst, PeanoMultiplication.mul_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh q i q hi'.1, FOL.term_subst_fresh m i q hi'.2]
  have h₁ : FOL.substAt φ i q' = (mul q m).equal (mul q' m) := by
    simp only [FOL.substAt, φ, FOL.equality_subst, PeanoMultiplication.mul_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh q i q' hi'.1, FOL.term_subst_fresh m i q' hi'.2]
  have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
    (FOL.LogicalAxiom.eqSubst φ i q q')
  rw [h₀, h₁] at h
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  exact .mp (.mp (.closed h) (FOL.Context.head [] (q.equal q')))
    (.closed (.logical (.eqRefl _)))

/-- Two explicit quotient/remainder equations have equal remainders whenever
their quotients are equal. Different quotients remain a separate obligation. -/
theorem remainders_of_quotient_equality (dividend q q' modulus r s : Peano.Term) :
    FormulaProves ((q.equal q').imp
      ((dividend.equal (add (mul q modulus) r)).imp
        ((dividend.equal (add (mul q' modulus) s)).imp (r.equal s)))) := by
  let eqQ : Peano.Formula := q.equal q'
  let eqR : Peano.Formula := dividend.equal (add (mul q modulus) r)
  let eqS : Peano.Formula := dividend.equal (add (mul q' modulus) s)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hq : FOL.Context Peano.Axiom [eqS, eqR, eqQ] eqQ :=
    FOL.Context.under (FOL.Context.under (FOL.Context.head [] eqQ) eqR) eqS
  have hr : FOL.Context Peano.Axiom [eqS, eqR, eqQ] eqR :=
    FOL.Context.under (FOL.Context.head [eqQ] eqR) eqS
  have hs : FOL.Context Peano.Axiom [eqS, eqR, eqQ] eqS :=
    FOL.Context.head [eqR, eqQ] eqS
  have hm : FOL.Context Peano.Axiom [eqS, eqR, eqQ]
      ((mul q modulus).equal (mul q' modulus)) :=
    .mp (.closed (mul_left_congr q q' modulus)) hq
  have ha : FOL.Context Peano.Axiom [eqS, eqR, eqQ]
      ((add (mul q modulus) r).equal (add (mul q' modulus) r)) :=
    .mp (.closed (add_left_congr r _ _)) hm
  have he : FOL.Context Peano.Axiom [eqS, eqR, eqQ]
      ((add (mul q' modulus) r).equal (add (mul q' modulus) s)) :=
    FOL.Context.eqTrans (FOL.Context.eqTrans (FOL.Context.eqSymm ha)
      (FOL.Context.eqSymm hr)) hs
  exact .mp (.closed (add_left_cancel (mul q' modulus) r s)) he

end PASoundness.PeanoAdditionCancellation
