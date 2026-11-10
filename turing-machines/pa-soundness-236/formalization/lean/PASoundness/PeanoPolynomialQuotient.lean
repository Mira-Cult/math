import PASoundness.PeanoMultiplicationAssociative

/-! PA-provable equality as a commutative semiring quotient. Every equality of
quotient terms recovers a PA derivation; no arithmetic soundness is used. -/
namespace PASoundness.PeanoPolynomialQuotient
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication
open PeanoAdditionAssociative PeanoMultiplicationAssociative

/-- Two terms are equivalent when their equality has a PA derivation. -/
def termSetoid : Setoid Peano.Term where
  r a b := FormulaProves (a.equal b)
  iseqv := ⟨fun a => .logical (.eqRefl a), fun h => .eqSymm h,
    fun h k => .eqTrans h k⟩

abbrev Poly := Quotient termSetoid

def cls (a : Peano.Term) : Poly := Quotient.mk termSetoid a

theorem cls_exact {a b : Peano.Term} (h : cls a = cls b) :
    FormulaProves (a.equal b) := Quotient.exact h

def addClass (a b : Poly) : Poly :=
  Quotient.liftOn₂ a b (fun x y => cls (Peano.add x y)) (by
    intro a b c d hac hbd
    apply Quotient.sound
    exact .eqTrans (.mp (add_left_congr b a c) hac) (.mp (add_right_congr c b d) hbd))

def mulClass (a b : Poly) : Poly :=
  Quotient.liftOn₂ a b (fun x y => cls (Peano.mul x y)) (by
    intro a b c d hac hbd
    apply Quotient.sound
    exact .eqTrans (.mp (PeanoAdditionCancellation.mul_left_congr a c b) hac)
      (.mp (mul_right_congr c b d) hbd))

instance : Zero Poly := ⟨cls Peano.zero⟩
instance : One Poly := ⟨cls (succ Peano.zero)⟩
instance : Add Poly := ⟨addClass⟩
instance : Mul Poly := ⟨mulClass⟩

@[simp] theorem cls_zero : cls Peano.zero = (0 : Poly) := rfl
@[simp] theorem cls_one : cls (succ Peano.zero) = (1 : Poly) := rfl
@[simp] theorem cls_add (a b : Peano.Term) : cls (Peano.add a b) = cls a + cls b := rfl
@[simp] theorem cls_mul (a b : Peano.Term) : cls (Peano.mul a b) = cls a * cls b := rfl

instance : CommSemiring Poly where
  nsmul := nsmulRec
  add_assoc := by
    intro a b c; induction a using Quotient.inductionOn; induction b using Quotient.inductionOn
    induction c using Quotient.inductionOn; exact Quotient.sound (add_assoc _ _ _)
  zero_add := by
    intro a; induction a using Quotient.inductionOn; exact Quotient.sound (zero_add _)
  add_zero := by
    intro a; induction a using Quotient.inductionOn; exact Quotient.sound (.axiom (.add_zero _))
  add_comm := by
    intro a b; induction a using Quotient.inductionOn; induction b using Quotient.inductionOn
    exact Quotient.sound (add_comm _ _)
  mul_assoc := by
    intro a b c; induction a using Quotient.inductionOn; induction b using Quotient.inductionOn
    induction c using Quotient.inductionOn; exact Quotient.sound (mul_assoc _ _ _)
  one_mul := by
    intro a; induction a using Quotient.inductionOn; exact Quotient.sound (one_mul _)
  mul_one := by
    intro a; induction a using Quotient.inductionOn
    exact Quotient.sound (.eqTrans (PeanoBetaProductIncrement.mul_comm _ _) (one_mul _))
  zero_mul := by
    intro a; induction a using Quotient.inductionOn; exact Quotient.sound (zero_mul _)
  mul_zero := by
    intro a; induction a using Quotient.inductionOn; exact Quotient.sound (.axiom (.mul_zero _))
  left_distrib := by
    intro a b c; induction a using Quotient.inductionOn; induction b using Quotient.inductionOn
    induction c using Quotient.inductionOn; exact Quotient.sound (mul_add_right _ _ _)
  right_distrib := by
    intro a b c; induction a using Quotient.inductionOn; induction b using Quotient.inductionOn
    induction c using Quotient.inductionOn; exact Quotient.sound (PeanoQuotientGap.mul_add_left _ _ _)
  mul_comm := by
    intro a b; induction a using Quotient.inductionOn; induction b using Quotient.inductionOn
    exact Quotient.sound (PeanoBetaProductIncrement.mul_comm _ _)

/-- Example: a polynomial identity is recovered as actual PA proof data. -/
theorem square_sum (a b : Peano.Term) :
    FormulaProves (((mul (add a b) (add a b))).equal
      (add (add (mul a a) (mul a b)) (add (mul b a) (mul b b)))) := by
  apply cls_exact
  simp only [cls_add, cls_mul]
  ring

end PASoundness.PeanoPolynomialQuotient
