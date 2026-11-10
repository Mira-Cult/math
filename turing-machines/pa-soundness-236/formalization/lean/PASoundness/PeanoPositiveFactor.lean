import PASoundness.PeanoEmptyBitSet
import PASoundness.PeanoOrderTotality
import PASoundness.PeanoAdditionCancellation
import PASoundness.PeanoMultiplyQuotientStep

/-! An object-level PA positivity implication for an explicit product.
Existential divisor witnesses and inverse-certificate packaging are separate. -/
namespace PASoundness.PeanoPositiveFactor
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic

private theorem or_elim {L : Language} {A : FOL.Formula L → Prop}
    {Γ : List (FOL.Formula L)} {φ ψ χ : FOL.Formula L}
    (h : FOL.Context A Γ (φ ⊔ ψ)) (hφ : FOL.Context A Γ (φ.imp χ))
    (hψ : FOL.Context A Γ (ψ.imp χ)) : FOL.Context A Γ χ := by
  apply FOL.Context.dne
  apply FOL.Context.deduction
  have hnφ : FOL.Context A (χ.not :: Γ) φ.not :=
    .mp (FOL.Context.under (FOL.Context.contrapose hφ) χ.not) (FOL.Context.head Γ χ.not)
  have hψ' : FOL.Context A (χ.not :: Γ) ψ :=
    .mp (FOL.Context.under h χ.not) hnφ
  exact .mp (FOL.Context.head Γ χ.not) (.mp (FOL.Context.under hψ χ.not) hψ')

/-- If a product is strictly positive, its explicit quotient factor is strictly
positive. The equality and strict bound remain literal PA antecedents. -/
theorem quotient_positive (c q m : Peano.Term) :
    FormulaProves ((less zero c).imp ((c.equal (mul q m)).imp (less zero q))) := by
  let P := less zero c
  let E := c.equal (mul q m)
  let Q := zero.equal q
  let L := less zero q
  let G := less q zero
  let Γ := [E,P]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hp : FOL.Context Peano.Axiom Γ P := FOL.Context.under (FOL.Context.head [] P) E
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.head _ _
  have hQ : FOL.Context Peano.Axiom Γ (Q.imp L) := by
    apply FOL.Context.deduction
    have hq : FOL.Context Peano.Axiom (Q :: Γ) (q.equal zero) :=
      FOL.Context.eqSymm (FOL.Context.head Γ Q)
    have hprod : FOL.Context Peano.Axiom (Q :: Γ) ((mul q m).equal zero) :=
      FOL.Context.eqTrans
        (.mp (.closed (PeanoAdditionCancellation.mul_left_congr q zero m)) hq)
        (.closed (PeanoMultiplication.zero_mul m))
    have hc : FOL.Context Peano.Axiom (Q :: Γ) (c.equal zero) :=
      FOL.Context.eqTrans (FOL.Context.under he Q) hprod
    have hlt : FOL.Context Peano.Axiom (Q :: Γ) (less zero zero) :=
      .mp (.mp (.closed (PeanoMultiplyQuotientStep.less_right_congr zero c zero)) hc)
        (FOL.Context.under hp Q)
    exact FOL.Context.explode L (.mp (.closed (PeanoOrderIrreflexive.less_self zero)) hlt)
  have hL : FOL.Context Peano.Axiom Γ (L.imp L) := by
    apply FOL.Context.deduction
    exact FOL.Context.head Γ L
  have hG : FOL.Context Peano.Axiom Γ (G.imp L) := by
    apply FOL.Context.deduction
    exact FOL.Context.explode L
      (.mp (.closed (PeanoEmptyBitSet.no_less_zero q)) (FOL.Context.head Γ G))
  have hQL : FOL.Context Peano.Axiom Γ ((Q ⊔ L).imp L) := by
    apply FOL.Context.deduction
    exact or_elim (FOL.Context.head Γ (Q ⊔ L))
      (FOL.Context.under hQ (Q ⊔ L)) (FOL.Context.under hL (Q ⊔ L))
  exact or_elim (.closed (PeanoOrderTotality.trichotomy_all zero q)) hQL hG

end PASoundness.PeanoPositiveFactor
