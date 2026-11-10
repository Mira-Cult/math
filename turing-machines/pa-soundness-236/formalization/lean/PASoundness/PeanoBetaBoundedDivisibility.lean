import PASoundness.PeanoCommonMultiple
import PASoundness.PeanoDivisibility
import PASoundness.PeanoBetaUniformPreserve

/-! Bounded divisibility invariants for a beta-modulus product, proved in PA.
The initial bounded-divisibility property remains an explicit hypothesis. -/
namespace PASoundness.PeanoBetaBoundedDivisibility
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic PeanoDivisibility

/-- Names 1,4,6 hold the beta parameter, product and bound respectively;
name 2 is bound as the index. -/
abbrev boundedDivisors : Peano.Formula := PeanoBetaUniformPreserve.boundedDivisors

/-- Multiplication preserves divisibility by every modulus below the bound.
If the factor mentions name 2, it varies with the bound index; otherwise this
is a common factor. No existence or positivity of the factor is assumed. -/
theorem bounded_divides_mul_term (factor : Peano.Term) : FormulaProves
    (boundedDivisors.imp (FOL.allAt 2
      ((less (.var 2) (.var 6)).imp
        (divides (modulus (.var 1) (.var 2)) (mul (.var 4) factor))))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.generalize 2
  · intro ψ hψ
    have h : ψ = boundedDivisors := by simpa using hψ
    subst ψ
    decide
  apply FOL.Context.deduction
  let L := less (.var 2) (.var 6)
  let M := modulus (.var 1) (.var 2)
  let Γ := [L, boundedDivisors]
  have hbound : FOL.Context Peano.Axiom Γ boundedDivisors :=
    FOL.Context.under (FOL.Context.head [] boundedDivisors) L
  have hsmall : FOL.Context Peano.Axiom Γ L := FOL.Context.head _ _
  have hdiv : FOL.Context Peano.Axiom Γ (divides M (.var 4)) :=
    .mp (FOL.Context.allSelf hbound) hsmall
  exact .mp (.closed (divides_mul M (.var 4) factor)) hdiv


/-- The concrete append increment is a multiple of every processed modulus.
The free names are code 0, parameter 1, product 4, bound 6, new index 7,
new value 8 and inverse 9. The increment is common to every bound index. -/
theorem bounded_divides_append_increment : FormulaProves
    (boundedDivisors.imp (FOL.allAt 2
      ((less (.var 2) (.var 6)).imp
        (divides (modulus (.var 1) (.var 2))
          (mul (.var 4) (mul (.var 9)
            (add (.var 8) (mul (mul (succ (.var 7)) (.var 1)) (.var 0))))))))) :=
  bounded_divides_mul_term (mul (.var 9)
    (add (.var 8) (mul (mul (succ (.var 7)) (.var 1)) (.var 0))))

/-- When the new index is the current bound (name 6), the actual CRT append
increment remains divisible by every processed modulus. -/
theorem bounded_divides_boundary_increment : FormulaProves
    (boundedDivisors.imp (FOL.allAt 2
      ((less (.var 2) (.var 6)).imp
        (divides (modulus (.var 1) (.var 2))
          (mul (.var 4) (mul (.var 9)
            (add (.var 8) (mul (mul (succ (.var 6)) (.var 1)) (.var 0))))))))) :=
  bounded_divides_mul_term (mul (.var 9)
    (add (.var 8) (mul (mul (succ (.var 6)) (.var 1)) (.var 0))))

/-- At the boundary `j=n`, the modulus at `j` divides the updated product. -/
theorem boundary_modulus_divides (j n c p : Peano.Term) :
    FormulaProves ((j.equal n).imp (divides (modulus c j) (mul p (modulus c n)))) := by
  let E := j.equal n
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hsucc : FOL.Context Peano.Axiom [E] ((succ n).equal (succ j)) :=
    FOL.Context.eqSymm (.mp (.closed (PeanoOrderIrreflexive.succ_congr j n))
      (FOL.Context.head [] E))
  have hmul : FOL.Context Peano.Axiom [E]
      ((mul (succ n) c).equal (mul (succ j) c)) :=
    .mp (.closed (PeanoAdditionCancellation.mul_left_congr _ _ c)) hsucc
  have hmod : FOL.Context Peano.Axiom [E] ((modulus c n).equal (modulus c j)) :=
    .mp (.closed (PeanoOrderIrreflexive.succ_congr _ _)) hmul
  exact .mp (.mp (.closed (PeanoCommonMultiple.DivisibilityBoundary.divisor_congr
    (modulus c n) (modulus c j) (mul p (modulus c n)))) hmod)
    (.closed (PeanoCommonMultiple.DivisibilityBoundary.factor_divides_product
      (modulus c n) p))

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

/-- After multiplying the old product by the new modulus at the current
bound, all old moduli and the new boundary modulus divide the new product. -/
theorem bounded_divides_next_product : FormulaProves
    (boundedDivisors.imp (FOL.allAt 2
      ((less (.var 2) (succ (.var 6))).imp
        (divides (modulus (.var 1) (.var 2))
          (mul (.var 4) (modulus (.var 1) (.var 6))))))) := by
  let L := less (.var 2) (.var 6)
  let L' := less (.var 2) (succ (.var 6))
  let E := (.var 2 : Peano.Term).equal (.var 6)
  let M := modulus (.var 1) (.var 2)
  let N := modulus (.var 1) (.var 6)
  let D' := divides M (mul (.var 4) N)
  let Γ := [L', boundedDivisors]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.generalize 2
  · intro ψ hψ
    have h : ψ = boundedDivisors := by simpa using hψ
    subst ψ
    decide
  apply FOL.Context.deduction
  have hbound : FOL.Context Peano.Axiom Γ boundedDivisors :=
    FOL.Context.under (FOL.Context.head [] boundedDivisors) L'
  have hsmall : FOL.Context Peano.Axiom Γ L' := FOL.Context.head _ _
  have hcases : FOL.Context Peano.Axiom Γ (E ⊔ L) :=
    .mp (.closed (PeanoCommonMultiple.BoundSplit.less_successor_cases (.var 2) (.var 6))) hsmall
  have he : FOL.Context Peano.Axiom Γ (E.imp D') :=
    .closed (boundary_modulus_divides (.var 2) (.var 6) (.var 1) (.var 4))
  have hl : FOL.Context Peano.Axiom Γ (L.imp D') := by
    apply FOL.Context.deduction
    have hold : FOL.Context Peano.Axiom (L :: Γ) boundedDivisors :=
      FOL.Context.under hbound L
    have hdiv : FOL.Context Peano.Axiom (L :: Γ) (divides M (.var 4)) :=
      .mp (FOL.Context.allSelf hold) (FOL.Context.head Γ L)
    exact .mp (.closed (divides_mul M (.var 4) N)) hdiv
  exact or_elim hcases he hl


/-- Both quantified divisibility invariants needed by one CRT update: the
append increment preserves all processed moduli, and the updated product
contains those moduli plus the newly processed boundary modulus. -/
theorem bounded_crt_divisibility_step : FormulaProves
    (boundedDivisors.imp
      ((FOL.allAt 2
          ((less (.var 2) (.var 6)).imp
            (divides (modulus (.var 1) (.var 2))
              (mul (.var 4) (mul (.var 9)
                (add (.var 8) (mul (mul (succ (.var 6)) (.var 1)) (.var 0)))))))) ⊓
       (FOL.allAt 2
          ((less (.var 2) (succ (.var 6))).imp
            (divides (modulus (.var 1) (.var 2))
              (mul (.var 4) (modulus (.var 1) (.var 6)))))))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have h : FOL.Context Peano.Axiom [boundedDivisors] boundedDivisors :=
    FOL.Context.head [] boundedDivisors
  exact FOL.Context.conjunctionIntro
    (.mp (.closed bounded_divides_boundary_increment) h)
    (.mp (.closed bounded_divides_next_product) h)

end PASoundness.PeanoBetaBoundedDivisibility
