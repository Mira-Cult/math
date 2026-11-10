import PASoundness.PeanoPolynomialQuotient
import PASoundness.PeanoBitWitnessIntroAll

/-! Object-level arithmetic for installing a bit at a power position. -/
namespace PASoundness.PeanoBitInsertion
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- PA derives the bit-row equation with quotient zero for `p + r`.
The remainder bound and the existence of a power trace are separate premises. -/
theorem inserted_row_equation (p r : Peano.Term) : FormulaProves
    ((add p r).equal (add (add (mul zero (add p p)) p) r)) := by
  apply PeanoPolynomialQuotient.cls_exact
  simp only [PeanoPolynomialQuotient.cls_add, PeanoPolynomialQuotient.cls_mul,
    PeanoPolynomialQuotient.cls_zero]
  ring

/-- PA derives that `p + r` has bit `n` when `p` has a literal power trace
at `n` and `r < p`. This installs the new bit; preservation of other bits
and the existence of a suitable power trace are separate obligations. -/
theorem inserted_bit (n p r : Peano.Term) : FormulaProves
    ((pow2 n p).imp ((less r p).imp (bitFormula (add p r) n))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let P := pow2 n p
  let R := less r p
  let Γ := [R, P]
  have hp : FOL.Context Peano.Axiom Γ P := .hypothesis (by simp [Γ])
  have hr : FOL.Context Peano.Axiom Γ R := .head _ _
  have hrow := FOL.Context.conjunctionIntro
    (FOL.Context.closed (inserted_row_equation p r) : FOL.Context Peano.Axiom Γ _) hr
  exact .mp (.mp (.closed (PeanoBitWitnessIntroAll.bit_of_witnesses_all
    (add p r) n p zero r)) hp) hrow

end PASoundness.PeanoBitInsertion

#print axioms PASoundness.PeanoBitInsertion.inserted_row_equation
#print axioms PASoundness.PeanoBitInsertion.inserted_bit
