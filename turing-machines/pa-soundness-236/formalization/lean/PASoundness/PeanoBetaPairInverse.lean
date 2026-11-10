import PASoundness.PeanoMultiplicationAssociative
import PASoundness.PeanoPolynomialQuotient

/-! Object-level PA identities and an explicit inverse certificate for two
beta moduli with a positive product-form parameter. This fixed-pair result does
not establish bounded CRT or trace extension. -/
namespace PASoundness.PeanoBetaPairInverse
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication
open PeanoMultiplicationAssociative PeanoBetaProductIncrement

/-- The key square identity, with all variables arbitrary PA terms. If the
beta parameter is `k*h`, this expresses `(a²*h)*(k*c) = (a*c)²` without
truncated subtraction or any positivity premise. -/
theorem square_factor_identity (a k h : Peano.Term) :
    FormulaProves ((mul (mul (mul a a) h) (mul k (mul k h))).equal
      (mul (mul a (mul k h)) (mul a (mul k h)))) := by
  let C := mul k h
  let K := mul (mul a a) h
  let A := mul a C
  have h₁ : FormulaProves ((mul K (mul k C)).equal (mul (mul K k) C)) :=
    FOL.Derivation.eqSymm (mul_assoc K k C)
  have h₂ : FormulaProves ((mul (mul K k) C).equal (mul (mul (mul a a) (mul h k)) C)) :=
    .mp (PeanoAdditionCancellation.mul_left_congr _ _ C) (mul_assoc (mul a a) h k)
  have h₃ : FormulaProves ((mul (mul (mul a a) (mul h k)) C).equal
      (mul (mul (mul a a) C) C)) :=
    .mp (PeanoAdditionCancellation.mul_left_congr _ _ C)
      (.mp (mul_right_congr (mul a a) _ _) (mul_comm h k))
  have h₄ : FormulaProves ((mul (mul (mul a a) C) C).equal (mul (mul a (mul a C)) C)) :=
    .mp (PeanoAdditionCancellation.mul_left_congr _ _ C) (mul_assoc a a C)
  have h₅ : FormulaProves ((mul (mul a (mul a C)) C).equal (mul (mul a (mul C a)) C)) :=
    .mp (PeanoAdditionCancellation.mul_left_congr _ _ C)
      (.mp (mul_right_congr a _ _) (mul_comm a C))
  have h₆ : FormulaProves ((mul (mul a (mul C a)) C).equal (mul (mul A a) C)) :=
    .mp (PeanoAdditionCancellation.mul_left_congr _ _ C)
      (FOL.Derivation.eqSymm (mul_assoc a C a))
  have h₇ : FormulaProves ((mul (mul A a) C).equal (mul A A)) := mul_assoc A a C
  exact FOL.Derivation.eqTrans (FOL.Derivation.eqTrans (FOL.Derivation.eqTrans
    (FOL.Derivation.eqTrans (FOL.Derivation.eqTrans (FOL.Derivation.eqTrans h₁ h₂) h₃) h₄) h₅) h₆) h₇

/-- A subtraction-free polynomial identity used to build an inverse
certificate. This is a PA derivation for arbitrary terms, not an inverse
existence or pairwise-coprimality theorem. -/
theorem predecessor_square_identity (d k : Peano.Term) :
    FormulaProves ((add (succ zero)
      (mul (add d k) (succ (succ d)))).equal
        (add (mul k (succ (succ d))) (mul (succ d) (succ d)))) := by
  let A := succ d
  let M := succ A
  let T := mul d A
  let U := mul k M
  have h₁ : FormulaProves ((add (succ zero) (mul (add d k) M)).equal
      (add (succ zero) (add (mul d M) U))) :=
    .mp (PeanoAdditionAssociative.add_right_congr _ _ _)
      (PeanoQuotientGap.mul_add_left d k M)
  have h₂ : FormulaProves ((add (succ zero) (add (mul d M) U)).equal
      (add (succ zero) (add (add T d) U))) :=
    .mp (PeanoAdditionAssociative.add_right_congr _ _ _)
      (.mp (PeanoAdditionAssociative.add_left_congr U _ _) (.axiom (.mul_succ d A)))
  have h₃ : FormulaProves ((add (succ zero) (add (add T d) U)).equal
      (add (add (succ zero) (add T d)) U)) :=
    FOL.Derivation.eqSymm (PeanoAdditionAssociative.add_assoc (succ zero) (add T d) U)
  have h₄ : FormulaProves ((add (add (succ zero) (add T d)) U).equal
      (add (add (add (succ zero) T) d) U)) :=
    .mp (PeanoAdditionAssociative.add_left_congr U _ _)
      (FOL.Derivation.eqSymm (PeanoAdditionAssociative.add_assoc (succ zero) T d))
  have h₅ : FormulaProves ((add (add (add (succ zero) T) d) U).equal
      (add (add (add (succ zero) d) T) U)) :=
    .mp (PeanoAdditionAssociative.add_left_congr U _ _)
      (PeanoMultiplyQuotientStep.swap_add_tail (succ zero) T d)
  have hOne : FormulaProves ((add (succ zero) d).equal A) :=
    FOL.Derivation.eqTrans (PeanoAdditionAssociative.add_comm (succ zero) d)
      (PeanoArithmetic.add_one d)
  have h₆ : FormulaProves ((add (add (add (succ zero) d) T) U).equal
      (add (add A T) U)) :=
    .mp (PeanoAdditionAssociative.add_left_congr U _ _)
      (.mp (PeanoAdditionAssociative.add_left_congr T _ _) hOne)
  have h₇ : FormulaProves ((add (add A T) U).equal (add (add T A) U)) :=
    .mp (PeanoAdditionAssociative.add_left_congr U _ _) (PeanoAdditionAssociative.add_comm A T)
  have h₈ : FormulaProves ((add (add T A) U).equal (add (add (mul A d) A) U)) :=
    .mp (PeanoAdditionAssociative.add_left_congr U _ _)
      (.mp (PeanoAdditionAssociative.add_left_congr A _ _) (mul_comm d A))
  have h₉ : FormulaProves ((add (add (mul A d) A) U).equal (add (mul A A) U)) :=
    .mp (PeanoAdditionAssociative.add_left_congr U _ _)
      (FOL.Derivation.eqSymm (.axiom (.mul_succ A d)))
  have h₁₀ : FormulaProves ((add (mul A A) U).equal (add U (mul A A))) :=
    PeanoAdditionAssociative.add_comm _ _
  exact FOL.Derivation.eqTrans (FOL.Derivation.eqTrans (FOL.Derivation.eqTrans
    (FOL.Derivation.eqTrans (FOL.Derivation.eqTrans (FOL.Derivation.eqTrans
      (FOL.Derivation.eqTrans (FOL.Derivation.eqTrans (FOL.Derivation.eqTrans
        h₁ h₂) h₃) h₄) h₅) h₆) h₇) h₈) h₉) h₁₀

/-- The central positive-form inverse identity, conditional only on an explicit
predecessor and a square-factor equation. It uses neither subtraction nor
semantic arithmetic. -/
theorem predecessor_inverse_identity (a d k t : Peano.Term) :
    FormulaProves ((a.equal (succ d)).imp
      (((mul k t).equal (mul a a)).imp
        ((add (succ zero) (mul (add d k) (succ a))).equal
          (mul k (add (succ a) t))))) := by
  let A := succ d
  let M := succ A
  let E := a.equal A
  let F := (mul k t).equal (mul a a)
  let Γ := [F, E]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.under (FOL.Context.head [] E) F
  have hf : FOL.Context Peano.Axiom Γ F := FOL.Context.head _ _
  have hm : FOL.Context Peano.Axiom Γ ((succ a).equal M) :=
    .mp (.closed (PeanoOrderIrreflexive.succ_congr a A)) he
  have hsq₁ : FOL.Context Peano.Axiom Γ ((mul a a).equal (mul A a)) :=
    .mp (.closed (PeanoAdditionCancellation.mul_left_congr a A a)) he
  have hsq₂ : FOL.Context Peano.Axiom Γ ((mul A a).equal (mul A A)) :=
    .mp (.closed (mul_right_congr A a A)) he
  have hkt : FOL.Context Peano.Axiom Γ ((mul k t).equal (mul A A)) :=
    FOL.Context.eqTrans (FOL.Context.eqTrans hf hsq₁) hsq₂
  have hl : FOL.Context Peano.Axiom Γ
      ((add (succ zero) (mul (add d k) (succ a))).equal
        (add (succ zero) (mul (add d k) M))) :=
    .mp (.closed (PeanoAdditionAssociative.add_right_congr _ _ _))
      (.mp (.closed (mul_right_congr (add d k) _ _)) hm)
  have hmid : FOL.Context Peano.Axiom Γ
      ((add (succ zero) (mul (add d k) M)).equal
        (add (mul k M) (mul k t))) :=
    FOL.Context.eqTrans (.closed (predecessor_square_identity d k))
      (.mp (.closed (PeanoAdditionAssociative.add_right_congr (mul k M) _ _))
        (FOL.Context.eqSymm hkt))
  have hr : FOL.Context Peano.Axiom Γ
      ((mul k (add M t)).equal (mul k (add (succ a) t))) :=
    .mp (.closed (mul_right_congr k _ _))
      (.mp (.closed (PeanoAdditionAssociative.add_left_congr t _ _))
        (FOL.Context.eqSymm hm))
  exact FOL.Context.eqTrans (FOL.Context.eqTrans (FOL.Context.eqTrans hl hmid)
    (.closed (FOL.Derivation.eqSymm (mul_add_right k M t)))) hr

/-- If `a*(k*h)` has a displayed predecessor, the pair of beta-modulus
components has the key positive-form equation. This does not construct the
predecessor, nor yet a full modular-inverse certificate. -/
theorem beta_pair_key_identity (a k h d : Peano.Term) :
    FormulaProves (((mul a (mul k h)).equal (succ d)).imp
      ((add (succ zero)
        (mul (add d (mul (mul a a) h)) (succ (mul a (mul k h))))).equal
        (mul (mul (mul a a) h)
          (add (succ (mul a (mul k h))) (mul k (mul k h)))))) := by
  let A := mul a (mul k h)
  let K := mul (mul a a) h
  let T := mul k (mul k h)
  let E := A.equal (succ d)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom [E] E := FOL.Context.head [] E
  exact .mp (.mp (.closed (predecessor_inverse_identity A d K T)) he)
    (.closed (square_factor_identity a k h))

open PeanoPolynomialQuotient

/-- Successor is addition of one in the proof-producing PA quotient. -/
theorem cls_succ (a : Peano.Term) : cls (succ a) = cls a + 1 := by
  apply Quotient.sound
  exact FOL.Derivation.eqSymm (PeanoArithmetic.add_one a)

/-- A universally valid rearrangement used to eliminate the leading one. -/
theorem successor_product_expansion (e t : Peano.Term) :
    FormulaProves ((mul (succ e) (succ (succ t))).equal
      (add (succ zero) (add (succ t) (mul e (succ (succ t)))))) := by
  apply cls_exact
  simp only [cls_add, cls_mul, cls_succ, cls_zero]
  ring

/-- A universally valid rearrangement converting a predecessor equation into
an explicit inverse certificate. -/
theorem inverse_product_expansion (e t : Peano.Term) :
    FormulaProves ((mul (add (succ t) (mul e (succ (succ t)))) (succ t)).equal
      (add (succ zero)
        (mul (add t (mul e (succ t))) (succ (succ t))))) := by
  apply cls_exact
  simp only [cls_add, cls_mul, cls_succ, cls_zero]
  ring

/-- From the displayed positive-form pair identity, construct explicit
nonnegative inverse witnesses. The equations used in this proof are PA
derivations, and the assumption remains an object-level antecedent. -/
theorem inverse_from_positive_identity (m h e t : Peano.Term) :
    FormulaProves (((add (succ zero) (mul h m)).equal
      (mul (succ e) (succ (succ t)))).imp
        ((mul m (mul h (succ t))).equal
          (add (succ zero) (mul (add t (mul e (succ t))) (succ (succ t)))))) := by
  let N := succ (succ t)
  let S := succ t
  let E := (add (succ zero) (mul h m)).equal (mul (succ e) N)
  let Γ := [E]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.head [] E
  have h₁ : FOL.Context Peano.Axiom Γ ((add (succ zero) (mul h m)).equal
      (add (succ zero) (add S (mul e N)))) :=
    FOL.Context.eqTrans he (.closed (successor_product_expansion e t))
  have h₂ : FOL.Context Peano.Axiom Γ ((mul h m).equal (add S (mul e N))) :=
    .mp (.closed (PeanoAdditionCancellation.add_left_cancel (succ zero) _ _)) h₁
  have h₃ : FOL.Context Peano.Axiom Γ
      ((mul m (mul h S)).equal (mul (mul h m) S)) := by
    have h : FormulaProves ((mul m (mul h S)).equal (mul (mul h m) S)) := by
      apply cls_exact
      simp only [cls_mul]
      ring
    exact .closed h
  have h₄ : FOL.Context Peano.Axiom Γ
      ((mul (mul h m) S).equal (mul (add S (mul e N)) S)) :=
    .mp (.closed (PeanoAdditionCancellation.mul_left_congr _ _ S)) h₂
  exact FOL.Context.eqTrans (FOL.Context.eqTrans h₃ h₄)
    (.closed (inverse_product_expansion e t))

/-- The inverse construction with all three arithmetic inputs explicit. It
constructs witnesses from equations; it does not assert those equations exist. -/
theorem inverse_from_predecessors (m h k n e t : Peano.Term) :
    FormulaProves (((add (succ zero) (mul h m)).equal (mul k n)).imp
      ((k.equal (succ e)).imp ((n.equal (succ (succ t))).imp
        ((mul m (mul h (succ t))).equal
          (add (succ zero) (mul (add t (mul e (succ t))) n)))))) := by
  let E := (add (succ zero) (mul h m)).equal (mul k n)
  let F := k.equal (succ e)
  let G := n.equal (succ (succ t))
  let Γ := [G,F,E]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom Γ E :=
    FOL.Context.under (FOL.Context.under (FOL.Context.head [] E) F) G
  have hf : FOL.Context Peano.Axiom Γ F := FOL.Context.under (FOL.Context.head [E] F) G
  have hg : FOL.Context Peano.Axiom Γ G := FOL.Context.head _ _
  have h₁ : FOL.Context Peano.Axiom Γ ((mul k n).equal (mul (succ e) n)) :=
    .mp (.closed (PeanoAdditionCancellation.mul_left_congr k (succ e) n)) hf
  have h₂ : FOL.Context Peano.Axiom Γ ((mul (succ e) n).equal
      (mul (succ e) (succ (succ t)))) :=
    .mp (.closed (mul_right_congr (succ e) n (succ (succ t)))) hg
  have hh : FOL.Context Peano.Axiom Γ ((add (succ zero) (mul h m)).equal
      (mul (succ e) (succ (succ t)))) := FOL.Context.eqTrans (FOL.Context.eqTrans he h₁) h₂
  have hcert : FOL.Context Peano.Axiom Γ
      ((mul m (mul h (succ t))).equal
        (add (succ zero) (mul (add t (mul e (succ t))) (succ (succ t))))) :=
    .mp (.closed (inverse_from_positive_identity m h e t)) hh
  have hrewrite : FOL.Context Peano.Axiom Γ
      ((add (succ zero) (mul (add t (mul e (succ t))) (succ (succ t)))).equal
        (add (succ zero) (mul (add t (mul e (succ t))) n))) :=
    .mp (.closed (PeanoAdditionAssociative.add_right_congr _ _ _))
      (.mp (.closed (mul_right_congr _ _ _)) (FOL.Context.eqSymm hg))
  exact FOL.Context.eqTrans hcert hrewrite

/-- An explicit positive pair identity yields a PA inverse certificate for the
pair of beta-modulus components. The three displayed predecessor equations
remain antecedents; their construction and bounded family version are separate. -/
theorem beta_pair_inverse_certificate (a k h d e t : Peano.Term) :
    FormulaProves (((mul a (mul k h)).equal (succ d)).imp
      (((mul (mul a a) h).equal (succ e)).imp
        (((add (succ (mul a (mul k h))) (mul k (mul k h))).equal (succ (succ t))).imp
          ((mul (succ (mul a (mul k h)))
              (mul (add d (mul (mul a a) h)) (succ t))).equal
            (add (succ zero)
              (mul (add t (mul e (succ t)))
                (add (succ (mul a (mul k h))) (mul k (mul k h))))))))) := by
  let A := mul a (mul k h)
  let K := mul (mul a a) h
  let T := mul k (mul k h)
  let M := succ A
  let N := add M T
  let H := add d K
  let E := A.equal (succ d)
  let F := K.equal (succ e)
  let G := N.equal (succ (succ t))
  let Γ := [G,F,E]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom Γ E :=
    FOL.Context.under (FOL.Context.under (FOL.Context.head [] E) F) G
  have hf : FOL.Context Peano.Axiom Γ F := FOL.Context.under (FOL.Context.head [E] F) G
  have hg : FOL.Context Peano.Axiom Γ G := FOL.Context.head _ _
  have hkey : FOL.Context Peano.Axiom Γ ((add (succ zero) (mul H M)).equal (mul K N)) :=
    .mp (.closed (beta_pair_key_identity a k h d)) he
  exact .mp (.mp (.mp (.closed (inverse_from_predecessors M H K N e t)) hkey) hf) hg

/-- The target modulus has an explicit predecessor as soon as the first
modulus component does. The only retained assumptions are the two displayed
predecessor equations. -/
theorem beta_pair_inverse_two_predecessors (a k h d e : Peano.Term) :
    FormulaProves (((mul a (mul k h)).equal (succ d)).imp
      (((mul (mul a a) h).equal (succ e)).imp
        ((mul (succ (mul a (mul k h)))
            (mul (add d (mul (mul a a) h)) (succ (add d (mul k (mul k h)))))).equal
          (add (succ zero)
            (mul (add (add d (mul k (mul k h)))
                       (mul e (succ (add d (mul k (mul k h))))))
              (add (succ (mul a (mul k h))) (mul k (mul k h)))))))) := by
  let A := mul a (mul k h)
  let K := mul (mul a a) h
  let T := mul k (mul k h)
  let N := add (succ A) T
  let E := A.equal (succ d)
  let F := K.equal (succ e)
  let Γ := [F,E]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.under (FOL.Context.head [] E) F
  have hf : FOL.Context Peano.Axiom Γ F := FOL.Context.head _ _
  have h₁ : FOL.Context Peano.Axiom Γ (N.equal (add (succ (succ d)) T)) :=
    .mp (.closed (PeanoAdditionAssociative.add_left_congr T _ _))
      (.mp (.closed (PeanoOrderIrreflexive.succ_congr _ _)) he)
  have h₂ : FormulaProves ((add (succ (succ d)) T).equal (succ (add (succ d) T))) :=
    PeanoAdditionAssociative.add_succ_left (succ d) T
  have h₃ : FormulaProves ((succ (add (succ d) T)).equal (succ (succ (add d T)))) :=
    .mp (PeanoOrderIrreflexive.succ_congr _ _) (PeanoAdditionAssociative.add_succ_left d T)
  have hn : FOL.Context Peano.Axiom Γ (N.equal (succ (succ (add d T)))) :=
    FOL.Context.eqTrans (FOL.Context.eqTrans h₁ (.closed h₂)) (.closed h₃)
  exact .mp (.mp (.mp (.closed (beta_pair_inverse_certificate a k h d e (add d T))) he) hf) hn

/-- Rewrite the second positive-form modulus into the exact modulus syntax at
index `i+k`. The two predecessor equations remain explicit antecedents. -/
theorem beta_modulus_pair_inverse (i k h d e : Peano.Term) :
    FormulaProves (((mul (succ i) (mul k h)).equal (succ d)).imp
      (((mul (mul (succ i) (succ i)) h).equal (succ e)).imp
        ((mul (CompactArithmetic.modulus (mul k h) i)
            (mul (add d (mul (mul (succ i) (succ i)) h))
              (succ (add d (mul k (mul k h)))))).equal
          (add (succ zero)
            (mul (add (add d (mul k (mul k h)))
                       (mul e (succ (add d (mul k (mul k h))))))
              (CompactArithmetic.modulus (mul k h) (add i k))))))) := by
  let A := succ i
  let C := mul k h
  let K := mul (mul A A) h
  let T := mul k C
  let M := succ (mul A C)
  let N := add M T
  let N' := CompactArithmetic.modulus C (add i k)
  let H := add d K
  let W := succ (add d T)
  let V := add (add d T) (mul e W)
  let E := (mul A C).equal (succ d)
  let F := K.equal (succ e)
  let Γ := [F,E]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.under (FOL.Context.head [] E) F
  have hf : FOL.Context Peano.Axiom Γ F := FOL.Context.head _ _
  have hcert : FOL.Context Peano.Axiom Γ ((mul M (mul H W)).equal
      (add (succ zero) (mul V N))) :=
    .mp (.mp (.closed (beta_pair_inverse_two_predecessors A k h d e)) he) hf
  have hn₁ : FormulaProves (N.equal (succ (add (mul A C) (mul k C)))) :=
    PeanoAdditionAssociative.add_succ_left (mul A C) (mul k C)
  have hn₂ : FormulaProves ((succ (add (mul A C) (mul k C))).equal
      (succ (mul (add A k) C))) :=
    .mp (PeanoOrderIrreflexive.succ_congr _ _)
      (FOL.Derivation.eqSymm (PeanoQuotientGap.mul_add_left A k C))
  have hn₃ : FormulaProves ((succ (mul (add A k) C)).equal N') :=
    .mp (PeanoOrderIrreflexive.succ_congr _ _)
      (.mp (PeanoAdditionCancellation.mul_left_congr _ _ C)
        (PeanoAdditionAssociative.add_succ_left i k))
  have hn : FormulaProves (N.equal N') := FOL.Derivation.eqTrans
    (FOL.Derivation.eqTrans hn₁ hn₂) hn₃
  have hr : FormulaProves ((add (succ zero) (mul V N)).equal (add (succ zero) (mul V N'))) :=
    .mp (PeanoAdditionAssociative.add_right_congr _ _ _) (.mp (mul_right_congr _ _ _) hn)
  exact FOL.Context.eqTrans hcert (.closed hr)

/-- A concrete predecessor for a product of three successor terms. -/
def triplePred (a b c : Peano.Term) : Peano.Term :=
  add (mul (add (mul a (succ b)) b) (succ c)) c

/-- PA verifies the concrete predecessor. -/
theorem triple_product_predecessor (a b c : Peano.Term) :
    FormulaProves ((mul (succ a) (mul (succ b) (succ c))).equal
      (succ (triplePred a b c))) := by
  apply cls_exact
  simp only [triplePred, cls_add, cls_mul, cls_succ]
  ring

/-- The same predecessor works for the left-associated product. -/
theorem triple_product_predecessor_left (a b c : Peano.Term) :
    FormulaProves ((mul (mul (succ a) (succ b)) (succ c)).equal
      (succ (triplePred a b c))) :=
  FOL.Derivation.eqTrans (mul_assoc (succ a) (succ b) (succ c))
    (triple_product_predecessor a b c)

/-- For positive difference `S k` and positive parameter factor `S h`, PA
constructs an explicit inverse certificate for the two exact beta moduli at
indices `i` and `i+S k` with beta parameter `(S k)*(S h)`.
This fixed-pair result does not establish a bounded family or trace extension. -/
theorem beta_modulus_pair_inverse_positive (i k h : Peano.Term) :
    let K := succ k
    let H := succ h
    let C := mul K H
    let A := succ i
    let P := mul (mul A A) H
    let T := mul K C
    let D := triplePred i k h
    let E := triplePred i i h
    let U := mul (add D P) (succ (add D T))
    let V := add (add D T) (mul E (succ (add D T)))
    FormulaProves ((mul (CompactArithmetic.modulus C i) U).equal
      (add (succ zero) (mul V (CompactArithmetic.modulus C (add i K))))) := by
  dsimp only
  exact .mp (.mp (beta_modulus_pair_inverse i (succ k) (succ h)
    (triplePred i k h) (triplePred i i h))
      (triple_product_predecessor i k h))
        (triple_product_predecessor_left i i h)

end PASoundness.PeanoBetaPairInverse
