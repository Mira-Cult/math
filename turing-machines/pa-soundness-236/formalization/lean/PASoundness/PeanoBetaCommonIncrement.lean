import PASoundness.PeanoBetaCodeExtension

/-! PA preservation of beta rows under an explicitly divisible common increment. -/
namespace PASoundness.PeanoBetaCommonIncrement
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic

/-- Equality of code terms transports the literal beta formula inside PA. -/
theorem beta_code_congr (b b' c i r : Peano.Term) :
    FormulaProves ((b.equal b').imp ((beta b c i r).imp (beta b' c i r))) := by
  obtain ⟨j, hj⟩ := FOL.fresh_for_term (add c (add i r))
  have hj' : j ∉ c.varFinset ∧ j ∉ i.varFinset ∧ j ∉ r.varFinset := by
    simpa [Peano.add, FirstOrder.Language.Term.varFinset] using hj
  let φ : Peano.Formula := beta (.var j) c i r
  have h₀ : FOL.substAt φ j b = beta b c i r := by
    simp only [FOL.substAt, φ, beta_subst, FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh c j b hj'.1, FOL.term_subst_fresh i j b hj'.2.1,
      FOL.term_subst_fresh r j b hj'.2.2]
  have h₁ : FOL.substAt φ j b' = beta b' c i r := by
    simp only [FOL.substAt, φ, beta_subst, FirstOrder.Language.Term.subst, ↓reduceIte,
      FOL.term_subst_fresh c j b' hj'.1, FOL.term_subst_fresh i j b' hj'.2.1,
      FOL.term_subst_fresh r j b' hj'.2.2]
  have h := FOL.Derivation.logical (Axiom := Peano.Axiom)
    (FOL.LogicalAxiom.eqSubst φ j b b')
  rw [h₀, h₁] at h
  exact h

/-- Given a literal beta row and an explicit PA equation witnessing that d is a
multiple of the row modulus, adding d preserves the row. -/
theorem beta_add_divisible (b c i r d t : Peano.Term) :
    FormulaProves ((beta b c i r).imp
      ((d.equal (mul t (modulus c i))).imp (beta (add b d) c i r))) := by
  let P := beta b c i r
  let E := d.equal (mul t (modulus c i))
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hp : FOL.Context Peano.Axiom [E, P] P :=
    FOL.Context.under (FOL.Context.head [] P) E
  have he : FOL.Context Peano.Axiom [E, P] E := FOL.Context.head _ _
  have hupdate : FOL.Context Peano.Axiom [E, P]
      (beta (add b (mul t (modulus c i))) c i r) :=
    .mp (.closed (PeanoBetaCodeExtension.beta_add_modulus_multiple b c i r t)) hp
  have hadd : FOL.Context Peano.Axiom [E, P]
      ((add b (mul t (modulus c i))).equal (add b d)) :=
    .mp (.closed (PeanoAdditionAssociative.add_right_congr b _ _)) (FOL.Context.eqSymm he)
  exact .mp (.mp (.closed (beta_code_congr _ _ c i r)) hadd) hupdate

/-- One increment preserves two beta rows when separate explicit PA equations
witness divisibility by their respective moduli. No common multiple is asserted
to exist. -/
theorem beta_two_rows_add_divisible (b c i r j s d t u : Peano.Term) :
    FormulaProves ((beta b c i r).imp ((beta b c j s).imp
      ((d.equal (mul t (modulus c i))).imp
        ((d.equal (mul u (modulus c j))).imp
          ((beta (add b d) c i r) ⊓ (beta (add b d) c j s)))))) := by
  let P := beta b c i r
  let Q := beta b c j s
  let E := d.equal (mul t (modulus c i))
  let F := d.equal (mul u (modulus c j))
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hp : FOL.Context Peano.Axiom [F, E, Q, P] P :=
    FOL.Context.under (FOL.Context.under (FOL.Context.under (FOL.Context.head [] P) Q) E) F
  have hq : FOL.Context Peano.Axiom [F, E, Q, P] Q :=
    FOL.Context.under (FOL.Context.under (FOL.Context.head [P] Q) E) F
  have he : FOL.Context Peano.Axiom [F, E, Q, P] E :=
    FOL.Context.under (FOL.Context.head [Q, P] E) F
  have hf : FOL.Context Peano.Axiom [F, E, Q, P] F := FOL.Context.head _ _
  exact FOL.Context.conjunctionIntro
    (.mp (.mp (.closed (beta_add_divisible b c i r d t)) hp) he)
    (.mp (.mp (.closed (beta_add_divisible b c j s d u)) hq) hf)

end PASoundness.PeanoBetaCommonIncrement
