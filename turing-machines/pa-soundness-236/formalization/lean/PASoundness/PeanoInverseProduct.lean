import PASoundness.PeanoMultiplicationAssociative

/-! Multiplicative closure of explicit modular inverse certificates in PA.
The certificates remain explicit hypotheses; this does not prove their
existence or a bounded Chinese remainder theorem. -/
namespace PASoundness.PeanoInverseProduct
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication
open PeanoAdditionAssociative PeanoMultiplicationAssociative

/-- PA rearranges the four displayed factors. -/
theorem mul_shuffle (p q u s : Peano.Term) :
    FormulaProves ((mul (mul p q) (mul u s)).equal (mul (mul p u) (mul q s))) := by
  have h₁ := mul_assoc p q (mul u s)
  have h₂ := FOL.Derivation.mp (mul_right_congr p _ _)
    (FOL.Derivation.eqSymm (mul_assoc q u s))
  have h₃ := FOL.Derivation.mp (mul_right_congr p _ _)
    (FOL.Derivation.mp (PeanoAdditionCancellation.mul_left_congr _ _ s)
      (PeanoBetaProductIncrement.mul_comm q u))
  have h₄ := FOL.Derivation.mp (mul_right_congr p _ _) (mul_assoc u q s)
  have h₅ := FOL.Derivation.eqSymm (mul_assoc p u (mul q s))
  exact FOL.Derivation.eqTrans (FOL.Derivation.eqTrans (FOL.Derivation.eqTrans
    (FOL.Derivation.eqTrans h₁ h₂) h₃) h₄) h₅

/-- PA expands the product of two terms of the form `1 + k*m` and
constructs the new nonnegative coefficient explicitly. -/
theorem inverse_product_expand (v t m : Peano.Term) :
    FormulaProves ((mul (add (succ zero) (mul v m)) (add (succ zero) (mul t m))).equal
      (add (succ zero) (mul (add (add t v) (mul (mul v t) m)) m))) := by
  let O : Peano.Term := succ zero
  let X := mul v m
  let Y := mul t m
  let Z := mul (mul (mul v t) m) m
  have h₁ : FormulaProves
      ((mul (add O X) (add O Y)).equal (add (mul O (add O Y)) (mul X (add O Y)))) :=
    PeanoQuotientGap.mul_add_left O X (add O Y)
  have h₂ : FormulaProves
      ((add (mul O (add O Y)) (mul X (add O Y))).equal (add (add O Y) (mul X (add O Y)))) :=
    .mp (add_left_congr (mul X (add O Y)) _ _) (one_mul (add O Y))
  have h₃ : FormulaProves
      ((add (add O Y) (mul X (add O Y))).equal
        (add (add O Y) (add (mul X O) (mul X Y)))) :=
    .mp (add_right_congr (add O Y) _ _) (mul_add_right X O Y)
  have hXO : FormulaProves ((mul X O).equal X) :=
    FOL.Derivation.eqTrans (PeanoBetaProductIncrement.mul_comm X O) (one_mul X)
  have hXY : FormulaProves ((mul X Y).equal Z) :=
    FOL.Derivation.eqTrans (mul_shuffle v m t m)
      (FOL.Derivation.eqSymm (mul_assoc (mul v t) m m))
  have h₄a : FormulaProves
      ((add (mul X O) (mul X Y)).equal (add X (mul X Y))) :=
    .mp (add_left_congr (mul X Y) _ _) hXO
  have h₄b : FormulaProves ((add X (mul X Y)).equal (add X Z)) :=
    .mp (add_right_congr X _ _) hXY
  have h₄ : FormulaProves
      ((add (add O Y) (add (mul X O) (mul X Y))).equal (add (add O Y) (add X Z))) :=
    .mp (add_right_congr (add O Y) _ _) (FOL.Derivation.eqTrans h₄a h₄b)
  have h₅ : FormulaProves ((add (add O Y) (add X Z)).equal (add O (add (add Y X) Z))) :=
    FOL.Derivation.eqTrans (add_assoc O Y (add X Z))
      (.mp (add_right_congr O _ _) (FOL.Derivation.eqSymm (add_assoc Y X Z)))
  have h₆ : FormulaProves ((add O (add (add Y X) Z)).equal
      (add O (add (mul (add t v) m) Z))) :=
    .mp (add_right_congr O _ _) (.mp (add_left_congr Z _ _)
      (FOL.Derivation.eqSymm (PeanoQuotientGap.mul_add_left t v m)))
  have h₇ : FormulaProves ((add O (add (mul (add t v) m) Z)).equal
      (add O (mul (add (add t v) (mul (mul v t) m)) m))) :=
    .mp (add_right_congr O _ _)
      (FOL.Derivation.eqSymm (PeanoQuotientGap.mul_add_left (add t v) (mul (mul v t) m) m))
  exact FOL.Derivation.eqTrans (FOL.Derivation.eqTrans (FOL.Derivation.eqTrans
    (FOL.Derivation.eqTrans (FOL.Derivation.eqTrans (FOL.Derivation.eqTrans h₁ h₂) h₃) h₄) h₅) h₆) h₇

/-- Multiplying two explicitly certified inverses gives an explicit inverse
certificate for the product. Both certificate equations are PA antecedents. -/
theorem inverse_product (p q u s v t m : Peano.Term) :
    FormulaProves (((mul p u).equal (add (succ zero) (mul v m))).imp
      (((mul q s).equal (add (succ zero) (mul t m))).imp
        ((mul (mul p q) (mul u s)).equal
          (add (succ zero) (mul (add (add t v) (mul (mul v t) m)) m))))) := by
  let E := (mul p u).equal (add (succ zero) (mul v m))
  let F := (mul q s).equal (add (succ zero) (mul t m))
  let Γ := [F, E]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.under (FOL.Context.head [] E) F
  have hf : FOL.Context Peano.Axiom Γ F := FOL.Context.head _ _
  have h₁ : FOL.Context Peano.Axiom Γ
      ((mul (mul p q) (mul u s)).equal (mul (mul p u) (mul q s))) :=
    .closed (mul_shuffle p q u s)
  have h₂ : FOL.Context Peano.Axiom Γ
      ((mul (mul p u) (mul q s)).equal (mul (add (succ zero) (mul v m)) (mul q s))) :=
    .mp (.closed (PeanoAdditionCancellation.mul_left_congr _ _ (mul q s))) he
  have h₃ : FOL.Context Peano.Axiom Γ
      ((mul (add (succ zero) (mul v m)) (mul q s)).equal
        (mul (add (succ zero) (mul v m)) (add (succ zero) (mul t m)))) :=
    .mp (.closed (mul_right_congr _ _ _)) hf
  exact FOL.Context.eqTrans (FOL.Context.eqTrans (FOL.Context.eqTrans h₁ h₂) h₃)
    (.closed (inverse_product_expand v t m))

end PASoundness.PeanoInverseProduct
