import PASoundness.PeanoPolynomialContext

/-! Remainders are unchanged when the dividend is shifted by a multiple of
the modulus, assuming both quotient/remainder rows are explicitly supplied. -/
namespace PASoundness.PeanoRemainderShiftUnique
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- PA proves that the remainders in the two displayed bounded rows coincide.
No existence of either row or positivity of the modulus is assumed here. -/
theorem remainder_shift_unique (a d m q k q' t s : Peano.Term) : FormulaProves
    ((a.equal (add (mul q m) t)).imp
      ((d.equal (mul k m)).imp
        (((add a d).equal (add (mul q' m) s)).imp
          ((less t m).imp ((less s m).imp (t.equal s)))))) := by
  let E : Peano.Formula := a.equal (add (mul q m) t)
  let D : Peano.Formula := d.equal (mul k m)
  let F : Peano.Formula := (add a d).equal (add (mul q' m) s)
  let T : Peano.Formula := less t m
  let S : Peano.Formula := less s m
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Γ := [S, T, F, D, E]
  have he : FOL.Context Peano.Axiom Γ E := .hypothesis (by simp [Γ])
  have hd : FOL.Context Peano.Axiom Γ D := .hypothesis (by simp [Γ])
  have hf : FOL.Context Peano.Axiom Γ F := .hypothesis (by simp [Γ])
  have ht : FOL.Context Peano.Axiom Γ T := .hypothesis (by simp [Γ])
  have hs : FOL.Context Peano.Axiom Γ S := .head _ _
  have hshift : FOL.Context Peano.Axiom Γ
      ((add a d).equal (add (mul (add q k) m) t)) := by
    apply PeanoPolynomialContext.cls_exact
    simp only [PeanoPolynomialContext.cls_add, PeanoPolynomialContext.cls_mul]
    have ha := PeanoPolynomialContext.cls_sound he
    have hm := PeanoPolynomialContext.cls_sound hd
    simp only [PeanoPolynomialContext.cls_add, PeanoPolynomialContext.cls_mul] at ha hm
    rw [ha, hm]
    ring
  have hboth : FOL.Context Peano.Axiom Γ (((add q k).equal q') ⊓ (t.equal s)) := .mp (.mp (.mp (.mp
    (.closed (PeanoQuotientGap.quotient_remainder_unique (add a d) (add q k) q' m t s))
      ht) hs) hshift) hf
  exact FOL.Context.conjunctionRight hboth

/-- Specialization to a set-bit row: if a code and its shifted code have
the displayed rows, PA identifies the old remainder with `u+r`. -/
theorem bit_remainder_shift (a d u q k q' t r : Peano.Term) : FormulaProves
    ((a.equal (add (mul q (add u u)) t)).imp
      ((d.equal (mul k (add u u))).imp
        (((add a d).equal (add (add (mul q' (add u u)) u) r)).imp
          ((less t (add u u)).imp ((less r u).imp (t.equal (add u r))))))) := by
  let M := add u u
  let E : Peano.Formula := a.equal (add (mul q M) t)
  let D : Peano.Formula := d.equal (mul k M)
  let F : Peano.Formula := (add a d).equal (add (add (mul q' M) u) r)
  let T : Peano.Formula := less t M
  let R : Peano.Formula := less r u
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Γ := [R,T,F,D,E]
  have he : FOL.Context Peano.Axiom Γ E := .hypothesis (by simp [Γ])
  have hd : FOL.Context Peano.Axiom Γ D := .hypothesis (by simp [Γ])
  have hf : FOL.Context Peano.Axiom Γ F := .hypothesis (by simp [Γ])
  have ht : FOL.Context Peano.Axiom Γ T := .hypothesis (by simp [Γ])
  have hr : FOL.Context Peano.Axiom Γ R := .head _ _
  have hbound : FOL.Context Peano.Axiom Γ (less (add u r) M) :=
    .mp (.closed (PeanoMultiplyQuotientStep.less_add_left r u u)) hr
  have hrow : FOL.Context Peano.Axiom Γ
      ((add a d).equal (add (mul q' M) (add u r))) :=
    FOL.Context.eqTrans hf (.closed (PeanoAdditionAssociative.add_assoc (mul q' M) u r))
  exact .mp (.mp (.mp (.mp (.mp
    (.closed (remainder_shift_unique a d M q k q' t (add u r))) he) hd) hrow) ht) hbound

end PASoundness.PeanoRemainderShiftUnique

#print axioms PASoundness.PeanoRemainderShiftUnique.remainder_shift_unique
#print axioms PASoundness.PeanoRemainderShiftUnique.bit_remainder_shift
