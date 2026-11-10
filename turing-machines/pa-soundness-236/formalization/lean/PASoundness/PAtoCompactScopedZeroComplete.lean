import PASoundness.PAtoCompactScopedSuccSubstFull
import PASoundness.PAtoCompactScopedZeroEqualityFull

/-! Finite K formula alignment under a retained zero graph. The proof handles
all nested formulas and arbitrary aliases of active bound-level names. -/
namespace PASoundness.PAtoCompactScopedZeroComplete

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedLogicalCongruence
open PASoundness.PAtoCompactScopedSuccSubstFull
open PASoundness.PAtoCompactTermSubstZeroInduction PASoundness.PAtoCompactSuccSubstSyntax
open PASoundness.PAtoCompactScopedZeroEqualityFull

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Build precisely the equality leaves occurring in a bounded source formula. -/
private noncomputable def zero_leaves (g : Formula) (x q d : Nat) (hqd : q < d)
    {n : Nat} (φ : Peano.language.BoundedFormula Nat n) :
    ScopedLeaves (retainedZero g q d) (singleSubst x (.var q)) (singleSubst x Peano.zero) φ := by
  induction φ with
  | falsum => exact .falsum
  | @equal n s t => exact .equal s t (scoped_zero_equal g x q d hqd s t)
  | rel r ts => exact nomatch r
  | imp a b ia ib => exact .imp ia ib
  | all body ih => exact .all ih

/-- Given a graph witness for zero, substitutions by its value name and zero
agree at every formula depth, including when active bound labels alias other
names. The graph remains an object-level antecedent; no graph totality or
semantic soundness is assumed. -/
noncomputable def scoped_zero_substitution
    (g : Formula) (x q d : Nat) (hqd : q < d)
    {n : Nat} (φ : Peano.language.BoundedFormula Nat n) (bound : Fin n → Nat) :
    GuardedBoth (retainedZero g q d)
      (scopedFormula n (φ.subst (singleSubst x (.var q))) bound)
      (scopedFormula n (φ.subst (singleSubst x Peano.zero)) bound) := by
  exact scoped_substitution (retainedZero g q d) (singleSubst x (.var q))
    (singleSubst x Peano.zero) (zero_leaves g x q d hqd φ) bound

/-- All PA formulas, including quantified ones, inherit the two finite K
implications under the retained zero graph. -/
noncomputable def formula_zero_substitution
    (g : Formula) (x q d : Nat) (hqd : q < d) (φ : Peano.Formula) :
    GuardedBoth (retainedZero g q d)
      (formula (FOL.substAt φ x (.var q))) (formula (FOL.substAt φ x Peano.zero)) := by
  change GuardedBoth (retainedZero g q d)
    (scopedFormula 0 (φ.subst (singleSubst x (.var q))) Fin.elim0)
    (scopedFormula 0 (φ.subst (singleSubst x Peano.zero)) Fin.elim0)
  exact scoped_zero_substitution g x q d hqd φ Fin.elim0

theorem formula_zero_forward_certificate
    (g : Formula) (x q d : Nat) (hqd : q < d) (φ : Peano.Formula) :
    theoremCode (certificate ((formula_zero_substitution g x q d hqd φ).1)) =
      imp (retainedZero g q d).encode
        (imp (formula (FOL.substAt φ x (.var q))).encode
          (formula (FOL.substAt φ x Peano.zero)).encode) := certificate_correct _

theorem formula_zero_backward_certificate
    (g : Formula) (x q d : Nat) (hqd : q < d) (φ : Peano.Formula) :
    theoremCode (certificate ((formula_zero_substitution g x q d hqd φ).2)) =
      imp (retainedZero g q d).encode
        (imp (formula (FOL.substAt φ x Peano.zero)).encode
          (formula (FOL.substAt φ x (.var q))).encode) := certificate_correct _

end PASoundness.PAtoCompactScopedZeroComplete

#print axioms PASoundness.PAtoCompactScopedZeroComplete.scoped_zero_substitution
#print axioms PASoundness.PAtoCompactScopedZeroComplete.formula_zero_substitution
#print axioms PASoundness.PAtoCompactScopedZeroComplete.formula_zero_forward_certificate
#print axioms PASoundness.PAtoCompactScopedZeroComplete.formula_zero_backward_certificate
