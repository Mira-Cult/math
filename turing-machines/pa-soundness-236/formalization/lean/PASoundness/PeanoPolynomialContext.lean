import PASoundness.PeanoMultiplicationAssociative

/-! Quotient PA terms by equality derivable in an explicit fixed proof context.
Polynomial reasoning in this semiring extracts a contextual PA derivation,
including when the proof uses equations among the context hypotheses. -/
namespace PASoundness.PeanoPolynomialContext
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication
open PeanoAdditionAssociative PeanoMultiplicationAssociative

/-- Equivalence uses actual PA derivations from the fixed context. -/
def termSetoid (Γ : List Peano.Formula) : Setoid Peano.Term where
  r a b := FOL.Context Peano.Axiom Γ (a.equal b)
  iseqv := ⟨fun a => .closed (.logical (.eqRefl a)), fun h => .eqSymm h,
    fun h k => .eqTrans h k⟩

abbrev Poly (Γ : List Peano.Formula) := Quotient (termSetoid Γ)

def cls (Γ : List Peano.Formula) (a : Peano.Term) : Poly Γ := Quotient.mk (termSetoid Γ) a

/-- Extract exactly the derivation from the same context, not a closed PA proof. -/
theorem cls_exact {Γ : List Peano.Formula} {a b : Peano.Term}
    (h : cls Γ a = cls Γ b) : FOL.Context Peano.Axiom Γ (a.equal b) := Quotient.exact h

/-- Insert an already derived contextual equation into the quotient. -/
theorem cls_sound {Γ : List Peano.Formula} {a b : Peano.Term}
    (h : FOL.Context Peano.Axiom Γ (a.equal b)) : cls Γ a = cls Γ b := Quotient.sound h

def addClass {Γ : List Peano.Formula} (a b : Poly Γ) : Poly Γ :=
  Quotient.liftOn₂ a b (fun x y => cls Γ (Peano.add x y)) (by
    intro a b c d hac hbd
    apply Quotient.sound
    exact .eqTrans (.mp (.closed (add_left_congr b a c)) hac)
      (.mp (.closed (add_right_congr c b d)) hbd))

def mulClass {Γ : List Peano.Formula} (a b : Poly Γ) : Poly Γ :=
  Quotient.liftOn₂ a b (fun x y => cls Γ (Peano.mul x y)) (by
    intro a b c d hac hbd
    apply Quotient.sound
    exact .eqTrans (.mp (.closed (PeanoAdditionCancellation.mul_left_congr a c b)) hac)
      (.mp (.closed (mul_right_congr c b d)) hbd))

instance (Γ : List Peano.Formula) : Zero (Poly Γ) := ⟨cls Γ Peano.zero⟩
instance (Γ : List Peano.Formula) : One (Poly Γ) := ⟨cls Γ (succ Peano.zero)⟩
instance (Γ : List Peano.Formula) : Add (Poly Γ) := ⟨addClass⟩
instance (Γ : List Peano.Formula) : Mul (Poly Γ) := ⟨mulClass⟩

@[simp] theorem cls_zero (Γ : List Peano.Formula) : cls Γ Peano.zero = (0 : Poly Γ) := rfl
@[simp] theorem cls_one (Γ : List Peano.Formula) : cls Γ (succ Peano.zero) = (1 : Poly Γ) := rfl
@[simp] theorem cls_add (Γ : List Peano.Formula) (a b : Peano.Term) :
    cls Γ (Peano.add a b) = cls Γ a + cls Γ b := rfl
@[simp] theorem cls_mul (Γ : List Peano.Formula) (a b : Peano.Term) :
    cls Γ (Peano.mul a b) = cls Γ a * cls Γ b := rfl

instance (Γ : List Peano.Formula) : CommSemiring (Poly Γ) where
  nsmul := nsmulRec
  add_assoc := by
    intro a b c; induction a using Quotient.inductionOn; induction b using Quotient.inductionOn
    induction c using Quotient.inductionOn; exact Quotient.sound (.closed (add_assoc _ _ _))
  zero_add := by
    intro a; induction a using Quotient.inductionOn; exact Quotient.sound (.closed (zero_add _))
  add_zero := by
    intro a; induction a using Quotient.inductionOn; exact Quotient.sound (.closed (.axiom (.add_zero _)))
  add_comm := by
    intro a b; induction a using Quotient.inductionOn; induction b using Quotient.inductionOn
    exact Quotient.sound (.closed (add_comm _ _))
  mul_assoc := by
    intro a b c; induction a using Quotient.inductionOn; induction b using Quotient.inductionOn
    induction c using Quotient.inductionOn; exact Quotient.sound (.closed (mul_assoc _ _ _))
  one_mul := by
    intro a; induction a using Quotient.inductionOn; exact Quotient.sound (.closed (one_mul _))
  mul_one := by
    intro a; induction a using Quotient.inductionOn
    exact Quotient.sound (.closed (.eqTrans (PeanoBetaProductIncrement.mul_comm _ _) (one_mul _)))
  zero_mul := by
    intro a; induction a using Quotient.inductionOn; exact Quotient.sound (.closed (zero_mul _))
  mul_zero := by
    intro a; induction a using Quotient.inductionOn; exact Quotient.sound (.closed (.axiom (.mul_zero _)))
  left_distrib := by
    intro a b c; induction a using Quotient.inductionOn; induction b using Quotient.inductionOn
    induction c using Quotient.inductionOn; exact Quotient.sound (.closed (mul_add_right _ _ _))
  right_distrib := by
    intro a b c; induction a using Quotient.inductionOn; induction b using Quotient.inductionOn
    induction c using Quotient.inductionOn; exact Quotient.sound (.closed (PeanoQuotientGap.mul_add_left _ _ _))
  mul_comm := by
    intro a b; induction a using Quotient.inductionOn; induction b using Quotient.inductionOn
    exact Quotient.sound (.closed (PeanoBetaProductIncrement.mul_comm _ _))

/-- Test the intended interface with a real object-level assumption: from a=b,
PA derives a(a+c)=b²+bc. `ring` operates in the context quotient. -/
theorem equality_assumption_example (a b c : Peano.Term) :
    FOL.Context Peano.Axiom [a.equal b]
      ((mul a (add a c)).equal (add (mul b b) (mul b c))) := by
  apply cls_exact
  simp only [cls_add, cls_mul]
  have hab : cls [a.equal b] a = cls [a.equal b] b :=
    cls_sound (FOL.Context.head [] _)
  rw [hab]
  ring

end PASoundness.PeanoPolynomialContext
