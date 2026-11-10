import PASoundness.PeanoBetaAppendRelation
import PASoundness.PeanoBetaTraceBound

/-! A common PA-provable bound for the old rows and the appended row.
This is a pointwise bound, not a sequence-existence theorem. -/
namespace PASoundness.PeanoBetaAppendBound
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaAppendRelation

def traceBound : Peano.Term :=
  add (modulus (.var 5) (.var 0)) (add (.var 6) (.var 6))

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

/-- The proposed appended value is below the successor of the common bound. -/
theorem appended_value_bounded : FormulaProves
    (less (add (.var 6) (.var 6)) (succ traceBound)) := by
  let q : Peano.Term := add (.var 6) (.var 6)
  let m : Peano.Term := modulus (.var 5) (.var 0)
  have h : FormulaProves (less q (add (succ q) m)) :=
    .mp (PeanoQuotientGap.less_add_right q (succ q) m)
      (PeanoPowerTransition.self_less_succ q)
  have he : FormulaProves ((add (succ q) m).equal (succ (add m q))) := by
    exact .eqTrans (PeanoAdditionAssociative.add_succ_left q m)
      (.mp (PeanoOrderIrreflexive.succ_congr (add q m) (add m q))
        (PeanoAdditionAssociative.add_comm q m))
  exact .mp (.mp (PeanoMultiplyQuotientStep.less_right_congr q (add (succ q) m)
    (succ (add m q))) he) h

/-- Every value satisfying the appended-row relation is at most `traceBound`.
Both alternatives preserve the same free row value at name 3. -/
theorem relation_bounded : FormulaProves
    (appendRelation.imp (less (.var 3) (succ traceBound))) := by
  let I := less (.var 2) (succ (.var 0))
  let B := beta (.var 4) (.var 5) (.var 2) (.var 3)
  let E := (.var 2 : Peano.Term).equal (succ (.var 0))
  let Q := (.var 3 : Peano.Term).equal (add (.var 6) (.var 6))
  let R := I ⊓ B
  let S := E ⊓ Q
  let T := less (.var 3) (succ traceBound)
  let Γ := [appendRelation]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hleft : FOL.Context Peano.Axiom Γ (R.imp T) := by
    apply FOL.Context.deduction
    have h : FOL.Context Peano.Axiom (R :: Γ) R := FOL.Context.head _ _
    exact .mp (.mp (.closed (PeanoBetaTraceBound.old_row_bound_with_extra
      (add (.var 6) (.var 6)))) (FOL.Context.conjunctionLeft h)) (FOL.Context.conjunctionRight h)
  have hright : FOL.Context Peano.Axiom Γ (S.imp T) := by
    apply FOL.Context.deduction
    have h : FOL.Context Peano.Axiom (S :: Γ) S := FOL.Context.head _ _
    have he : FOL.Context Peano.Axiom (S :: Γ)
        ((add (.var 6) (.var 6)).equal (.var 3)) :=
      FOL.Context.eqSymm (FOL.Context.conjunctionRight h)
    exact .mp (.mp (.closed (PeanoQuotientGap.less_left_congr
      (add (.var 6) (.var 6)) (.var 3) (succ traceBound))) he)
        (.closed appended_value_bounded)
  have hcases : FOL.Context Peano.Axiom Γ (R ⊔ S) := by
    change FOL.Context Peano.Axiom [R ⊔ S] (R ⊔ S)
    exact FOL.Context.head [] _
  exact or_elim hcases hleft hright

/-- PA obtains a bound on the very same witness supplied by append-row
totality. Both the index limit and the bound are explicit terms. -/
theorem bounded_append_rows : FormulaProves
    (FOL.allAt 2 ((less (.var 2) (succ (succ (.var 0)))).imp
      (FOL.existsAt 3 (appendRelation ⊓ less (.var 3) (succ traceBound))))) := by
  let H := appendRelation
  let T := FOL.existsAt 3 (H ⊓ less (.var 3) (succ traceBound))
  have hbody : FormulaProves (H.imp T) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    have hh : FOL.Context Peano.Axiom [H] H := FOL.Context.head [] H
    have hl : FOL.Context Peano.Axiom [H] (less (.var 3) (succ traceBound)) :=
      .mp (.closed relation_bounded) hh
    have hc : FOL.Context Peano.Axiom [H] (H ⊓ less (.var 3) (succ traceBound)) :=
      FOL.Context.conjunctionIntro hh hl
    have hi := FOL.Derivation.existsIntro (A := Peano.Axiom)
      (H ⊓ less (.var 3) (succ traceBound)) 3 (.var 3)
    exact .mp (.closed (by simpa only [SyntaxTransport.substAt_self] using hi)) hc
  have hfresh : 3 ∉ T.freeVarFinset := by
    simp [T, FOL.existsAt, SyntaxTransport.allAt_freeVars,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]
  have helim := PeanoBitPositionReduction.exists_elim 3 hfresh hbody
  apply FOL.Derivation.generalize
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  let L := less (.var 2) (succ (succ (.var 0)))
  have hinst : FOL.Context Peano.Axiom [L] (L.imp (FOL.existsAt 3 H)) :=
    FOL.Context.allSelf (.closed PeanoBetaAppendRelation.append_rows_total)
  exact .mp (.closed helim) (.mp hinst (FOL.Context.head [] L))

end PASoundness.PeanoBetaAppendBound

#print axioms PASoundness.PeanoBetaAppendBound.appended_value_bounded
#print axioms PASoundness.PeanoBetaAppendBound.relation_bounded
#print axioms PASoundness.PeanoBetaAppendBound.bounded_append_rows
