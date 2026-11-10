import PASoundness.PeanoQuotientGap
import PASoundness.PeanoOneMul
import PASoundness.PeanoBetaCommonIncrement

/-! Explicit common modulus products for beta-code updates in PA. -/
namespace PASoundness.PeanoBetaProductIncrement
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic

/-- A successor in the first multiplication argument distributes in PA. -/
theorem succ_mul (a b : Peano.Term) :
    FormulaProves ((mul (succ a) b).equal (add (mul a b) b)) := by
  have h₁ := FOL.Derivation.mp
    (PeanoAdditionCancellation.mul_left_congr (succ a) (add a (succ zero)) b)
    (FOL.Derivation.eqSymm (PeanoArithmetic.add_one a))
  have h₂ := PeanoQuotientGap.mul_add_left a (succ zero) b
  have h₃ := FOL.Derivation.mp
    (PeanoAdditionAssociative.add_right_congr (mul a b) (mul (succ zero) b) b)
    (PeanoArithmetic.one_mul b)
  exact FOL.Derivation.eqTrans (FOL.Derivation.eqTrans h₁ h₂) h₃

/-- Genuine PA derivation of multiplication commutativity, for arbitrary terms. -/
theorem mul_comm (a b : Peano.Term) : FormulaProves ((mul a b).equal (mul b a)) := by
  obtain ⟨i, hi⟩ := FOL.fresh_for_term b
  let w : Peano.Term := .var i
  let φ : Peano.Formula := (mul w b).equal (mul b w)
  have hbase : FormulaProves (FOL.substAt φ i zero) := by
    have h := FOL.Derivation.eqTrans (PeanoMultiplication.zero_mul b)
      (FOL.Derivation.eqSymm (.axiom (.mul_zero b)))
    simpa only [FOL.substAt, φ, w, FOL.equality_subst, mul_subst, PeanoArithmetic.zero_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte, FOL.term_subst_fresh b i zero hi] using h
  have hstep : FormulaProves (φ.imp (FOL.substAt φ i (succ w))) := by
    have h : FormulaProves (φ.imp ((mul (succ w) b).equal (mul b (succ w)))) := by
      apply FOL.Context.closeEmpty
      apply FOL.Context.deduction
      have hc : FOL.Context Peano.Axiom [φ] ((add (mul w b) b).equal (add (mul b w) b)) :=
        .mp (.closed (PeanoAdditionAssociative.add_left_congr b _ _)) (FOL.Context.head [] φ)
      exact FOL.Context.eqTrans (FOL.Context.eqTrans (.closed (succ_mul w b)) hc)
        (FOL.Context.eqSymm (.closed (.axiom (.mul_succ b w))))
    simpa only [FOL.substAt, φ, w, FOL.equality_subst, mul_subst, succ_subst,
      FirstOrder.Language.Term.subst, ↓reduceIte, FOL.term_subst_fresh b i (succ (.var i)) hi] using h
  have hall : FormulaProves (FOL.allAt i φ) :=
    .mp (.mp (.axiom (.induction φ i)) hbase) (.generalize i hstep)
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim φ i a)) hall
  simpa only [FOL.substAt, φ, w, FOL.equality_subst, mul_subst,
    FirstOrder.Language.Term.subst, ↓reduceIte, FOL.term_subst_fresh b i a hi] using h

/-- The explicit product of two row moduli preserves both literal beta rows.
The construction uses no assumed divisibility equations: the two quotient
witnesses are the opposite moduli, and PA proves the needed commutation. -/
theorem beta_two_rows_add_product (b c i r j s : Peano.Term) :
    FormulaProves ((beta b c i r).imp ((beta b c j s).imp
      ((beta (add b (mul (modulus c j) (modulus c i))) c i r) ⊓
       (beta (add b (mul (modulus c j) (modulus c i))) c j s)))) := by
  let P := beta b c i r
  let Q := beta b c j s
  let M := modulus c i
  let N := modulus c j
  let D := mul N M
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hp : FOL.Context Peano.Axiom [Q, P] P := FOL.Context.under (FOL.Context.head [] P) Q
  have hq : FOL.Context Peano.Axiom [Q, P] Q := FOL.Context.head _ _
  have he : FOL.Context Peano.Axiom [Q, P] (D.equal (mul N M)) :=
    .closed (.logical (.eqRefl D))
  have hf : FOL.Context Peano.Axiom [Q, P] (D.equal (mul M N)) := .closed (mul_comm N M)
  exact .mp (.mp (.mp (.mp
    (.closed (PeanoBetaCommonIncrement.beta_two_rows_add_divisible b c i r j s D N M)) hp) hq) he) hf

end PASoundness.PeanoBetaProductIncrement
