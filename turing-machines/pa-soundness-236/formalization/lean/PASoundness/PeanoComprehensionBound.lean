import PASoundness.PeanoQuotientGap
import PASoundness.PeanoPowerTransition

/-! A common strict bound for the input code and the free position used in
the non-alias AX8 comprehension branch. This arithmetic lemma by itself does
not move an input code under a binder or establish any AX8 instance. -/
namespace PASoundness.PeanoComprehensionBound
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- The displayed input code lies below the common bound, even if its term
shares variables with the position term. -/
theorem code_below_bound (a b : Peano.Term) :
    FormulaProves (less a (add a (succ b))) := by
  have h : FormulaProves (less a (add (succ a) b)) :=
    .mp (PeanoQuotientGap.less_add_right a (succ a) b)
      (PeanoPowerTransition.self_less_succ a)
  have he : FormulaProves ((add (succ a) b).equal (add a (succ b))) :=
    .eqTrans (PeanoAdditionAssociative.add_succ_left a b)
      (.eqSymm (.axiom (.add_succ a b)))
  exact .mp (.mp (PeanoMultiplyQuotientStep.less_right_congr a _ _) he) h

/-- The free position lies below the same bound. -/
theorem position_below_bound (a b : Peano.Term) :
    FormulaProves (less b (add a (succ b))) := by
  have h : FormulaProves (less b (add (succ b) a)) :=
    .mp (PeanoQuotientGap.less_add_right b (succ b) a)
      (PeanoPowerTransition.self_less_succ b)
  have he : FormulaProves ((add (succ b) a).equal (add a (succ b))) :=
    PeanoAdditionAssociative.add_comm (succ b) a
  exact .mp (.mp (PeanoMultiplyQuotientStep.less_right_congr b _ _) he) h

end PASoundness.PeanoComprehensionBound

#print axioms PASoundness.PeanoComprehensionBound.code_below_bound
#print axioms PASoundness.PeanoComprehensionBound.position_below_bound
