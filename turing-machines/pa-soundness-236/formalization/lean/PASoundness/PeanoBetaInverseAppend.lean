import PASoundness.PeanoMultiplicationAssociative

/-! A beta row can be appended from an explicit modular-inverse certificate.
All arithmetic below is derived inside PA; existence of the certificate and
preservation of arbitrarily many old rows are separate obligations. -/
namespace PASoundness.PeanoBetaInverseAppend
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic
open PeanoAdditionAssociative PeanoMultiplicationAssociative

/-- The explicit append equation over arbitrary PA terms. The first hypothesis
is an inverse certificate; the second exposes the modulus predecessor. -/
theorem append_equation (b p u v m t r : Peano.Term) :
    FormulaProves (((mul p u).equal (add (succ zero) (mul v m))).imp
      ((m.equal (succ t)).imp
        ((add b (mul p (mul u (add r (mul t b))))).equal
          (add (mul (add b (mul v (add r (mul t b)))) m) r)))) := by
  let H := add r (mul t b)
  let J := mul (mul v H) m
  let E := (mul p u).equal (add (succ zero) (mul v m))
  let S := m.equal (succ t)
  let Γ := [S, E]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.under (FOL.Context.head [] E) S
  have hs : FOL.Context Peano.Axiom Γ S := FOL.Context.head _ _
  have h₁ : FOL.Context Peano.Axiom Γ
      ((add b (mul p (mul u H))).equal (add b (mul (mul p u) H))) :=
    .closed (.mp (add_right_congr b _ _)
      (FOL.Derivation.eqSymm (mul_assoc p u H)))
  have h₂ : FOL.Context Peano.Axiom Γ
      ((add b (mul (mul p u) H)).equal
        (add b (mul (add (succ zero) (mul v m)) H))) :=
    .mp (.closed (add_right_congr b _ _))
      (.mp (.closed (PeanoAdditionCancellation.mul_left_congr _ _ H)) he)
  have h₃ : FOL.Context Peano.Axiom Γ
      ((add b (mul (add (succ zero) (mul v m)) H)).equal
        (add b (add H J))) := by
    have h₃a := PeanoQuotientGap.mul_add_left (succ zero) (mul v m) H
    have h₃b := FOL.Derivation.mp (add_left_congr (mul (mul v m) H) _ _)
      (one_mul H)
    have h₃c : FormulaProves ((mul (mul v m) H).equal J) := by
      have h := FOL.Derivation.eqTrans (mul_assoc v m H)
        (FOL.Derivation.mp (mul_right_congr v _ _) (PeanoBetaProductIncrement.mul_comm m H))
      exact FOL.Derivation.eqTrans h (FOL.Derivation.eqSymm (mul_assoc v H m))
    have h₃d := FOL.Derivation.mp (add_right_congr H _ _) h₃c
    exact .closed (.mp (add_right_congr b _ _)
      (FOL.Derivation.eqTrans (FOL.Derivation.eqTrans h₃a h₃b) h₃d))
  have h₄ : FOL.Context Peano.Axiom Γ
      ((add b (add H J)).equal (add (add (add b r) (mul t b)) J)) :=
    .closed (FOL.Derivation.eqTrans (FOL.Derivation.eqSymm (add_assoc b H J))
      (.mp (add_left_congr J _ _) (FOL.Derivation.eqSymm (add_assoc b r (mul t b)))))
  have h₅ : FOL.Context Peano.Axiom Γ
      ((add (add (add b r) (mul t b)) J).equal
        (add (add (add b (mul t b)) r) J)) :=
    .closed (.mp (add_left_congr J _ _) (PeanoMultiplyQuotientStep.swap_add_tail b r (mul t b)))
  have htb : FOL.Context Peano.Axiom Γ
      ((add b (mul t b)).equal (mul m b)) := by
    have hh : FOL.Context Peano.Axiom Γ ((mul m b).equal (mul (succ t) b)) :=
      .mp (.closed (PeanoAdditionCancellation.mul_left_congr m (succ t) b)) hs
    exact FOL.Context.eqTrans (.closed (add_comm b (mul t b)))
      (FOL.Context.eqSymm (FOL.Context.eqTrans hh (.closed (PeanoBetaProductIncrement.succ_mul t b))))
  have h₆ : FOL.Context Peano.Axiom Γ
      ((add (add (add b (mul t b)) r) J).equal (add (add (mul m b) r) J)) :=
    .mp (.closed (add_left_congr J _ _))
      (.mp (.closed (add_left_congr r _ _)) htb)
  have h₇ : FOL.Context Peano.Axiom Γ
      ((add (add (mul m b) r) J).equal (add (add (mul m b) J) r)) :=
    .closed (PeanoMultiplyQuotientStep.swap_add_tail (mul m b) r J)
  have h₈ : FOL.Context Peano.Axiom Γ
      ((add (add (mul m b) J) r).equal (add (add (mul b m) J) r)) :=
    .closed (.mp (add_left_congr r _ _)
      (.mp (add_left_congr J _ _) (PeanoBetaProductIncrement.mul_comm m b)))
  have h₉ : FOL.Context Peano.Axiom Γ
      ((add (add (mul b m) J) r).equal (add (mul (add b (mul v H)) m) r)) :=
    .closed (.mp (add_left_congr r _ _)
      (FOL.Derivation.eqSymm (PeanoQuotientGap.mul_add_left b (mul v H) m)))
  exact FOL.Context.eqTrans (FOL.Context.eqTrans (FOL.Context.eqTrans
    (FOL.Context.eqTrans (FOL.Context.eqTrans (FOL.Context.eqTrans
    (FOL.Context.eqTrans (FOL.Context.eqTrans h₁ h₂) h₃) h₄) h₅) h₆) h₇) h₈) h₉

/-- An explicit inverse certificate supplies a new beta row. The bound and
both displayed arithmetic equations remain hypotheses in the PA proof. -/
theorem beta_append (b p u v c i t r : Peano.Term) :
    FormulaProves (((mul p u).equal (add (succ zero) (mul v (modulus c i)))).imp
      (((modulus c i).equal (succ t)).imp ((less r (modulus c i)).imp
        (beta (add b (mul p (mul u (add r (mul t b))))) c i r)))) := by
  let M := modulus c i
  let H := add r (mul t b)
  let E := (mul p u).equal (add (succ zero) (mul v M))
  let S := M.equal (succ t)
  let R := less r M
  let Γ := [R, S, E]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom Γ E :=
    FOL.Context.under (FOL.Context.under (FOL.Context.head [] E) S) R
  have hs : FOL.Context Peano.Axiom Γ S := FOL.Context.under (FOL.Context.head [E] S) R
  have hr : FOL.Context Peano.Axiom Γ R := FOL.Context.head _ _
  have hrow : FOL.Context Peano.Axiom Γ
      ((add b (mul p (mul u H))).equal (add (mul (add b (mul v H)) M) r)) :=
    .mp (.mp (.closed (append_equation b p u v M t r)) he) hs
  exact .mp (.mp (.closed (PeanoPowerExistenceBase.beta_intro
    (add b (mul p (mul u H))) c i r (add b (mul v H)))) hrow) hr

/-- The literal modulus is already a successor, so no independent predecessor
assumption is needed for a beta row. Certificate existence remains open. -/
theorem beta_append_literal (b p u v c i r : Peano.Term) :
    FormulaProves (((mul p u).equal (add (succ zero) (mul v (modulus c i)))).imp
      ((less r (modulus c i)).imp
        (beta (add b (mul p (mul u (add r (mul (mul (succ i) c) b))))) c i r))) := by
  let T := mul (succ i) c
  let E := (mul p u).equal (add (succ zero) (mul v (modulus c i)))
  let R := less r (modulus c i)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom [R, E] E := FOL.Context.under (FOL.Context.head [] E) R
  have hr : FOL.Context Peano.Axiom [R, E] R := FOL.Context.head _ _
  have ht : FOL.Context Peano.Axiom [R, E] ((modulus c i).equal (succ T)) :=
    .closed (.logical (.eqRefl _))
  exact .mp (.mp (.mp (.closed (beta_append b p u v c i T r)) he) ht) hr

/-- The same explicit increment preserves one old beta row while appending a
new one, when the old modulus is an explicitly witnessed factor of `p`.
No inverse certificate or common factor is asserted to exist. -/
theorem preserve_and_append (b p q u v c i old r s : Peano.Term) :
    FormulaProves ((beta b c old s).imp
      (((mul p u).equal (add (succ zero) (mul v (modulus c i)))).imp
        ((p.equal (mul q (modulus c old))).imp
          ((less r (modulus c i)).imp
            ((beta (add b (mul p (mul u (add r (mul (mul (succ i) c) b))))) c old s) ⊓
             (beta (add b (mul p (mul u (add r (mul (mul (succ i) c) b))))) c i r)))))) := by
  let M := modulus c old
  let N := modulus c i
  let H := add r (mul (mul (succ i) c) b)
  let D := mul p (mul u H)
  let P := beta b c old s
  let E := (mul p u).equal (add (succ zero) (mul v N))
  let F := p.equal (mul q M)
  let R := less r N
  let Γ := [R, F, E, P]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hp : FOL.Context Peano.Axiom Γ P :=
    FOL.Context.under (FOL.Context.under (FOL.Context.under (FOL.Context.head [] P) E) F) R
  have he : FOL.Context Peano.Axiom Γ E :=
    FOL.Context.under (FOL.Context.under (FOL.Context.head [P] E) F) R
  have hf : FOL.Context Peano.Axiom Γ F := FOL.Context.under (FOL.Context.head [E, P] F) R
  have hr : FOL.Context Peano.Axiom Γ R := FOL.Context.head _ _
  have h₁ : FOL.Context Peano.Axiom Γ (D.equal (mul (mul q M) (mul u H))) :=
    .mp (.closed (PeanoAdditionCancellation.mul_left_congr p (mul q M) (mul u H))) hf
  have h₂ : FormulaProves ((mul (mul q M) (mul u H)).equal (mul q (mul M (mul u H)))) :=
    mul_assoc q M (mul u H)
  have h₃ : FormulaProves ((mul q (mul M (mul u H))).equal (mul q (mul (mul u H) M))) :=
    .mp (mul_right_congr q _ _) (PeanoBetaProductIncrement.mul_comm M (mul u H))
  have h₄ : FormulaProves ((mul q (mul (mul u H) M)).equal (mul (mul q (mul u H)) M)) :=
    FOL.Derivation.eqSymm (mul_assoc q (mul u H) M)
  have hdiv : FOL.Context Peano.Axiom Γ (D.equal (mul (mul q (mul u H)) M)) :=
    FOL.Context.eqTrans (FOL.Context.eqTrans (FOL.Context.eqTrans h₁ (.closed h₂))
      (.closed h₃)) (.closed h₄)
  have hold : FOL.Context Peano.Axiom Γ (beta (add b D) c old s) :=
    .mp (.mp (.closed (PeanoBetaCommonIncrement.beta_add_divisible
      b c old s D (mul q (mul u H)))) hp) hdiv
  have hnew : FOL.Context Peano.Axiom Γ (beta (add b D) c i r) :=
    .mp (.mp (.closed (beta_append_literal b p u v c i r)) he) hr
  exact FOL.Context.conjunctionIntro hold hnew

end PASoundness.PeanoBetaInverseAppend
