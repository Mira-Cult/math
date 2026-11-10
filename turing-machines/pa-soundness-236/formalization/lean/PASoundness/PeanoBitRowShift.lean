import PASoundness.PeanoPolynomialContext

/-! An object-level arithmetic identity used in bit-row preservation. -/
namespace PASoundness.PeanoBitRowShift
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- Given an explicit bit-row equation, PA derives the corresponding equation
after adding a multiple of the doubled power. The remainder is unchanged. This
does not assert that a bit exists, that a power is divisible by a doubled
smaller power, or that this update reflects bit membership. -/
theorem shift_row (a p q r k : Peano.Term) :
    FormulaProves ((a.equal (add (add (mul q (add p p)) p) r)).imp
      ((add a (mul k (add p p))).equal
        (add (add (mul (add q k) (add p p)) p) r))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply PeanoPolynomialContext.cls_exact
  simp only [PeanoPolynomialContext.cls_add, PeanoPolynomialContext.cls_mul]
  have h := PeanoPolynomialContext.cls_sound
    (FOL.Context.head [] (a.equal (add (add (mul q (add p p)) p) r)))
  simp only [PeanoPolynomialContext.cls_add, PeanoPolynomialContext.cls_mul] at h
  rw [h]
  ring

end PASoundness.PeanoBitRowShift

#print axioms PASoundness.PeanoBitRowShift.shift_row
