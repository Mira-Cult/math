import PASoundness.PeanoBetaBound
import PASoundness.PeanoPolynomialContext

/-! A PA bound for a row of a finite beta trace. This proves neither trace
extension nor existence of a common code. -/

namespace PASoundness.PeanoBetaTraceBound
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic
open PeanoPolynomialContext

private theorem cls_succ (Γ : List Peano.Formula) (a : Peano.Term) :
    cls Γ (succ a) = cls Γ a + 1 := by
  apply cls_sound
  exact .closed (.eqSymm (PeanoArithmetic.add_one a))

private theorem less_index_syntax : less (.var 2) (succ (.var 0)) =
    FOL.existsAt 20 ((add (.var 2) (succ (.var 20))).equal (succ (.var 0))) := by
  simp [CompactArithmetic.less, CompactArithmetic.lessTemplate, CompactArithmetic.exAt,
    CompactArithmetic.v, FOL.existsAt, FOL.allAt, Peano.add, Peano.succ,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  constructor
  · congr 1
    funext i
    fin_cases i
    · rfl
    · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
      congr 1
      funext j
      fin_cases j
      rfl
  · rfl

/-- For `i ≤ n`, every beta value at index `i` is strictly less than the
modulus at index `n`. Here `n=0`, `i=2`, `r=3`, `B=4`, `C=5` are variable
names; 20 is a locally eliminated gap witness. -/
theorem old_row_bound : FormulaProves
    ((less (.var 2) (succ (.var 0))).imp
      ((beta (.var 4) (.var 5) (.var 2) (.var 3)).imp
        (less (.var 3) (modulus (.var 5) (.var 0))))) := by
  let i : Peano.Term := .var 2
  let n : Peano.Term := .var 0
  let r : Peano.Term := .var 3
  let b : Peano.Term := .var 4
  let c : Peano.Term := .var 5
  let d : Peano.Term := .var 20
  let E := (add i (succ d)).equal (succ n)
  let H := beta b c i r
  let T := less r (modulus c n)
  have hrow : FormulaProves (E.imp (H.imp T)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [H, E]
    have he : FOL.Context Peano.Axiom Γ E :=
      FOL.Context.under (FOL.Context.head [] E) H
    have he' : FOL.Context Peano.Axiom Γ ((succ (add i d)).equal (succ n)) :=
      FOL.Context.eqTrans (.closed (.eqSymm (.axiom (.add_succ i d)))) he
    have hin : FOL.Context Peano.Axiom Γ ((add i d).equal n) :=
      .mp (.closed (.axiom (.succ_injective (add i d) n))) he'
    have hm : FOL.Context Peano.Axiom Γ
        ((add (modulus c i) (mul d c)).equal (modulus c n)) := by
      apply cls_exact
      have hin' : cls Γ (add i d) = cls Γ n := cls_sound hin
      simp only [cls_add] at hin'
      simp only [modulus, cls_succ, cls_add, cls_mul]
      rw [← hin']
      ring
    have hr : FOL.Context Peano.Axiom Γ (less r (modulus c i)) :=
      .mp (.closed (PeanoBetaBound.beta_remainder_bound_all b c i r)) (FOL.Context.head _ _)
    have hr' : FOL.Context Peano.Axiom Γ (less r (add (modulus c i) (mul d c))) :=
      .mp (.closed (PeanoQuotientGap.less_add_right r (modulus c i) (mul d c))) hr
    exact .mp (.mp (.closed (PeanoMultiplyQuotientStep.less_right_congr r
      (add (modulus c i) (mul d c)) (modulus c n))) hm) hr'
  have hfresh : 20 ∉ (H.imp T).freeVarFinset := by decide
  have hex := PeanoBitPositionReduction.exists_elim 20 hfresh hrow
  simpa only [E, H, T, i, n, r, b, c, d, ← less_index_syntax] using hex

/-- The same row is at most `modulus(C,n)+q`, for any PA term `q`.
This form allows a separate appended value to be included in the common bound. -/
theorem old_row_bound_with_extra (q : Peano.Term) : FormulaProves
    ((less (.var 2) (succ (.var 0))).imp
      ((beta (.var 4) (.var 5) (.var 2) (.var 3)).imp
        (less (.var 3) (succ (add (modulus (.var 5) (.var 0)) q))))) := by
  let I := less (.var 2) (succ (.var 0))
  let H := beta (.var 4) (.var 5) (.var 2) (.var 3)
  let m := modulus (.var 5) (.var 0)
  let r : Peano.Term := .var 3
  let w := add m q
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hr : FOL.Context Peano.Axiom [H, I] (less r m) :=
    .mp (.mp (.closed old_row_bound) (FOL.Context.under (FOL.Context.head [] I) H))
      (FOL.Context.head _ _)
  have hw : FOL.Context Peano.Axiom [H, I] (less r w) :=
    .mp (.closed (PeanoQuotientGap.less_add_right r m q)) hr
  exact .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all r w (succ w))) hw)
    (.closed (PeanoPowerTransition.self_less_succ w))

end PASoundness.PeanoBetaTraceBound
