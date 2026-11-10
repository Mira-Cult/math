import PASoundness.PeanoBetaPairInverse
import PASoundness.PeanoDivisibility
import PASoundness.PeanoPositiveFactor
import PASoundness.PeanoPositivePredecessor

/-! A beta-modulus inverse certificate transported along an explicit positive
factorization, then generalized by eliminating the divisibility and positive
predecessor witnesses. This is a fixed-pair theorem, not bounded CRT. -/
namespace PASoundness.PeanoBetaPairDivisible
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic
open PeanoBetaPairInverse PeanoPolynomialContext

/-- A successor is addition of one in a fixed PA proof context. -/
theorem contextual_cls_succ (Γ : List Peano.Formula) (a : Peano.Term) :
    cls Γ (succ a) = cls Γ a + 1 := by
  apply cls_sound
  exact .closed (.eqSymm (PeanoArithmetic.add_one a))

/-- Transport the explicit pair inverse along an object-level equality
`c=(S k)*(S h)`. The predecessor witness `h` is explicit in this lemma. -/
theorem factorized_pair_inverse (i k h c : Peano.Term) :
    let K := succ k
    let H := succ h
    let C := mul K H
    let A := succ i
    let P := mul (mul A A) H
    let T := mul K C
    let D := triplePred i k h
    let E := triplePred i i h
    let U := mul (add D P) (succ (add D T))
    let V := add (add D T) (mul E (succ (add D T)))
    FormulaProves ((c.equal C).imp
      ((mul (modulus c i) U).equal
        (add (succ zero) (mul V (modulus c (add i K)))))) := by
  dsimp only
  let K := succ k
  let H := succ h
  let C := mul K H
  let A := succ i
  let P := mul (mul A A) H
  let T := mul K C
  let D := triplePred i k h
  let E := triplePred i i h
  let U := mul (add D P) (succ (add D T))
  let V := add (add D T) (mul E (succ (add D T)))
  let F := c.equal C
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply cls_exact
  have hc : cls [F] c = cls [F] C := cls_sound (FOL.Context.head [] F)
  have hv := cls_sound (Γ := [F]) (.closed (beta_modulus_pair_inverse_positive i k h))
  simp only [CompactArithmetic.modulus, cls_mul, cls_add, contextual_cls_succ] at hv ⊢
  rw [hc]
  simpa only [C, K, H, cls_mul, contextual_cls_succ] using hv

/-- The exact two-modulus inverse formula at free names 0 (index), 1
(parameter), and 2 (positive index gap predecessor). -/
def inverseBody (u v : Peano.Term) : Peano.Formula :=
  (mul (modulus (.var 1) (.var 0)) u).equal
    (add (succ zero) (mul v (modulus (.var 1) (add (.var 0) (succ (.var 2))))))

def inverseTemplate : Peano.Formula :=
  FOL.existsAt 3 (FOL.existsAt 4 (inverseBody (.var 3) (.var 4)))

/-- The positive-factor witness explicitly yields existential inverse witnesses.
This is a fixed-variable interface; divisibility and positivity elimination are
separate proof obligations. -/
theorem factorized_pair_inverse_exists :
    FormulaProves ((((.var 1 : Peano.Term).equal
      (mul (succ (.var 2)) (succ (.var 5))))).imp inverseTemplate) := by
  let i : Peano.Term := .var 0
  let k : Peano.Term := .var 2
  let h : Peano.Term := .var 5
  let c : Peano.Term := .var 1
  let K := succ k
  let H := succ h
  let C := mul K H
  let A := succ i
  let P := mul (mul A A) H
  let T := mul K C
  let D := triplePred i k h
  let E := triplePred i i h
  let U := mul (add D P) (succ (add D T))
  let V := add (add D T) (mul E (succ (add D T)))
  let F := c.equal C
  have hcert : FOL.Context Peano.Axiom [F] (inverseBody U V) :=
    .mp (.closed (factorized_pair_inverse i k h c)) (FOL.Context.head [] F)
  let body := inverseBody U (.var 4)
  have hsubst : FOL.substAt body 4 V = inverseBody U V := by
    simp [FOL.substAt, body, inverseBody, U, V, D, E, P, T, A, K, H, C, i, k, h,
      FOL.equality_subst, add_subst, mul_subst, succ_subst, modulus, triplePred, PeanoArithmetic.zero_subst,
      FirstOrder.Language.Term.subst]
  have hex4 : FOL.Context Peano.Axiom [F] (FOL.existsAt 4 body) := by
    apply FOL.Context.mp (.closed (FOL.Derivation.existsIntro body 4 V))
    rw [hsubst]
    exact hcert
  have hsubst3 : FOL.substAt (FOL.existsAt 4 (inverseBody (.var 3) (.var 4))) 3 U =
      FOL.existsAt 4 body := by
    simp [FOL.substAt, body, inverseBody, U, D, P, T, A, K, H, C, i, k, h,
      FOL.existsAt, FOL.allAt,
      modulus, triplePred, Peano.add, Peano.mul, Peano.succ, Peano.zero,
      FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
      FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.relabelAux]
    repeat' first
      | rfl
      | constructor
      | (congr 1; funext i; fin_cases i <;>
          dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.mp (.closed (FOL.Derivation.existsIntro
    (FOL.existsAt 4 (inverseBody (.var 3) (.var 4))) 3 U))
  rw [hsubst3]
  exact hex4

/-- A quotient with an explicit predecessor gives the factorization needed by
the pair inverse. Both equations are object-level PA antecedents. -/
theorem quotient_predecessor_pair_inverse :
    FormulaProves ((((.var 1 : Peano.Term).equal (mul (.var 6) (succ (.var 2))))).imp
      (((.var 6 : Peano.Term).equal (succ (.var 5))).imp inverseTemplate)) := by
  let c : Peano.Term := .var 1
  let q : Peano.Term := .var 6
  let k : Peano.Term := .var 2
  let h : Peano.Term := .var 5
  let G := c.equal (mul q (succ k))
  let Q := q.equal (succ h)
  let Γ := [Q,G]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hg : FOL.Context Peano.Axiom Γ G := FOL.Context.under (FOL.Context.head [] G) Q
  have hq : FOL.Context Peano.Axiom Γ Q := FOL.Context.head _ _
  have h₁ : FOL.Context Peano.Axiom Γ ((mul q (succ k)).equal (mul (succ h) (succ k))) :=
    .mp (.closed (PeanoAdditionCancellation.mul_left_congr q (succ h) (succ k))) hq
  have h₂ : FormulaProves ((mul (succ h) (succ k)).equal (mul (succ k) (succ h))) :=
    PeanoBetaProductIncrement.mul_comm _ _
  have hf : FOL.Context Peano.Axiom Γ (c.equal (mul (succ k) (succ h))) :=
    FOL.Context.eqTrans (FOL.Context.eqTrans hg h₁) (.closed h₂)
  exact .mp (.closed factorized_pair_inverse_exists) hf

/-- Exact binder-renamed form of the capture-safe divisibility formula. -/
theorem divides_succ_variable :
    PeanoDivisibility.divides (succ (.var 2)) (.var 1) =
      FOL.existsAt 6 ((.var 1 : Peano.Term).equal (mul (.var 6) (succ (.var 2)))) := by
  simp [PeanoDivisibility.divides, PeanoDivisibility.dividesTemplate, FOL.existsAt, FOL.allAt,
    Peano.mul, Peano.succ, Peano.zero, FirstOrder.Language.Term.equal,
    FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst,
    FirstOrder.Language.Term.relabel, FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.subst, FirstOrder.Language.BoundedFormula.relabel,
    FirstOrder.Language.BoundedFormula.mapTermRel, FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

/-- Exact predecessor formula for quotient variable 6, with fresh binder 5. -/
theorem predecessor_variable :
    PeanoPositivePredecessor.hasPredecessor (.var 6) =
      FOL.existsAt 5 ((.var 6 : Peano.Term).equal (succ (.var 5))) := by
  simp [PeanoPositivePredecessor.hasPredecessor, PeanoPositivePredecessor.predecessorTemplate,
    FOL.existsAt, FOL.allAt, Peano.succ, Peano.zero, FirstOrder.Language.Term.equal,
    FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst,
    FirstOrder.Language.Term.relabel, FirstOrder.Language.BoundedFormula.not,
    FirstOrder.Language.BoundedFormula.subst, FirstOrder.Language.BoundedFormula.relabel,
    FirstOrder.Language.BoundedFormula.mapTermRel, FirstOrder.Language.BoundedFormula.relabelAux]
  rfl

/-- Eliminate the predecessor witness without capturing the inverse target. -/
theorem quotient_with_predecessor :
    FormulaProves ((PeanoPositivePredecessor.hasPredecessor (.var 6)).imp
      ((((.var 1 : Peano.Term).equal (mul (.var 6) (succ (.var 2))))).imp inverseTemplate)) := by
  let G : Peano.Formula := (.var 1 : Peano.Term).equal (mul (.var 6) (succ (.var 2)))
  let Q : Peano.Formula := (.var 6 : Peano.Term).equal (succ (.var 5))
  have h : FormulaProves (Q.imp (G.imp inverseTemplate)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hq : FOL.Context Peano.Axiom [G,Q] Q := FOL.Context.under (FOL.Context.head [] Q) G
    have hg : FOL.Context Peano.Axiom [G,Q] G := FOL.Context.head _ _
    exact .mp (.mp (.closed quotient_predecessor_pair_inverse) hg) hq
  have hf : 5 ∉ (G.imp inverseTemplate).freeVarFinset := by decide
  have h' := PeanoBitPositionReduction.exists_elim 5 hf h
  simpa only [predecessor_variable, G, Q] using h'

/-- If the displayed quotient multiplies the gap to a positive parameter,
the exact two beta moduli have inverse witnesses. -/
theorem positive_quotient_inverse :
    FormulaProves ((((.var 1 : Peano.Term).equal (mul (.var 6) (succ (.var 2))))).imp
      ((less zero (.var 1)).imp inverseTemplate)) := by
  let G : Peano.Formula := (.var 1 : Peano.Term).equal (mul (.var 6) (succ (.var 2)))
  let L : Peano.Formula := less zero (.var 1)
  let Γ := [L,G]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hg : FOL.Context Peano.Axiom Γ G := FOL.Context.under (FOL.Context.head [] G) L
  have hl : FOL.Context Peano.Axiom Γ L := FOL.Context.head _ _
  have hp : FOL.Context Peano.Axiom Γ (less zero (.var 6)) :=
    .mp (.mp (.closed (PeanoPositiveFactor.quotient_positive (.var 1) (.var 6)
      (succ (.var 2)))) hl) hg
  have hex : FOL.Context Peano.Axiom Γ (PeanoPositivePredecessor.hasPredecessor (.var 6)) :=
    .mp (.closed (PeanoPositivePredecessor.positive_has_predecessor (.var 6))) hp
  exact .mp (.mp (.closed quotient_with_predecessor) hex) hg

/-- PA proves that for a positive parameter divisible by the positive index
gap, the exact pair of beta moduli has an inverse certificate. This proves one
pair only; it does not establish a bounded CRT family or trace extension. -/
theorem divisible_positive_inverse_vars :
    FormulaProves ((PeanoDivisibility.divides (succ (.var 2)) (.var 1)).imp
      ((less zero (.var 1)).imp inverseTemplate)) := by
  let L : Peano.Formula := less zero (.var 1)
  have hf : 6 ∉ (L.imp inverseTemplate).freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 6 hf positive_quotient_inverse
  simpa only [divides_succ_variable, L] using h

/-- Universally closed PA theorem, covering every parameter, index and positive
gap with the stated divisibility and positivity antecedents. -/
theorem divisible_positive_inverse_all :
    FormulaProves (FOL.allAt 0 (FOL.allAt 1 (FOL.allAt 2
      ((PeanoDivisibility.divides (succ (.var 2)) (.var 1)).imp
        ((less zero (.var 1)).imp inverseTemplate))))) :=
  .generalize 0 (.generalize 1 (.generalize 2 divisible_positive_inverse_vars))

end PASoundness.PeanoBetaPairDivisible
