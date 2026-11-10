import PASoundness.PeanoQuotientGap

/-! A literal bit-row equation cannot hold below its power. The result is
derived inside PA for arbitrary terms, with no power-existence or bit semantics
premise. -/

namespace PASoundness.PeanoBitBelowOrder
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- A code with the displayed one-bit quotient/remainder equation cannot be
strictly smaller than its displayed power. All four terms may share variables. -/
theorem row_not_below (a p q r : Peano.Term) :
    FormulaProves (((a.equal (add (add (mul q (add p p)) p) r))).imp
      (less a p).not) := by
  let t := mul q (add p p)
  let w := add (add t p) r
  let E := a.equal w
  let L := less a p
  let Γ := [L, E]
  have hreorder : FormulaProves (w.equal (add p (add t r))) := by
    exact FOL.Derivation.eqTrans
      (.mp (PeanoAdditionAssociative.add_left_congr r (add t p) (add p t))
        (PeanoAdditionAssociative.add_comm t p))
      (PeanoAdditionAssociative.add_assoc p t r)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom Γ E := .hypothesis (by simp [Γ])
  have hl : FOL.Context Peano.Axiom Γ L := FOL.Context.head _ _
  have he' : FOL.Context Peano.Axiom Γ (a.equal (add p (add t r))) :=
    FOL.Context.eqTrans he (.closed hreorder)
  have hl' : FOL.Context Peano.Axiom Γ (less (add p (add t r)) p) :=
    .mp (.mp (.closed (PeanoQuotientGap.less_left_congr a (add p (add t r)) p)) he') hl
  exact .mp (.closed (PeanoQuotientGap.not_less_add p (add t r))) hl'

/-- Equivalently, a strict upper bound excludes the displayed bit-row equation. -/
theorem below_excludes_row (a p q r : Peano.Term) :
    FormulaProves ((less a p).imp
      (a.equal (add (add (mul q (add p p)) p) r)).not) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let E := a.equal (add (add (mul q (add p p)) p) r)
  let L := less a p
  have he : FOL.Context Peano.Axiom [E, L] E := FOL.Context.head _ _
  have hl : FOL.Context Peano.Axiom [E, L] L := .hypothesis (by simp)
  exact .mp (.mp (.closed (row_not_below a p q r)) he) hl

end PASoundness.PeanoBitBelowOrder

#print axioms PASoundness.PeanoBitBelowOrder.row_not_below
#print axioms PASoundness.PeanoBitBelowOrder.below_excludes_row
