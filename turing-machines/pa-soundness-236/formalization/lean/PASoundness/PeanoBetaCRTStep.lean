import PASoundness.PeanoBetaInverseAppend
import PASoundness.PeanoInverseProduct
import PASoundness.PeanoDivisibility

/-! One object-level PA CRT invariant step, with explicit row, divisibility,
and inverse-certificate hypotheses. This is a pointwise step, not bounded CRT
or a trace-existence theorem. -/
namespace PASoundness.PeanoBetaCRTStep
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic

/-- Given a beta row at `old`, a product `p` with an explicit old-modulus
factor, an inverse certificate for the new modulus, and a bounded target row,
update the code and multiply the product by the new modulus. Two further
explicit certificates, for `p` and the new modulus against an arbitrary future
modulus, give a certificate for the updated product against that future modulus.
The stated equations are all object-level PA hypotheses; no certificates or
bounded family are asserted to exist. -/
theorem update_with_future_inverse
    (b p q u v c i old r s uf vf ui vi future : Peano.Term) :
    let M := modulus c i
    let O := modulus c old
    let J := modulus c future
    let B := add b (mul p (mul u (add r (mul (mul (succ i) c) b))))
    let P := mul p M
    let T := add (add vi vf) (mul (mul vf vi) J)
    FormulaProves ((beta b c old s).imp
      (((mul p u).equal (add (succ zero) (mul v M))).imp
        ((p.equal (mul q O)).imp ((less r M).imp
          (((mul p uf).equal (add (succ zero) (mul vf J))).imp
            (((mul M ui).equal (add (succ zero) (mul vi J))).imp
              (((beta B c old s) ⊓ (beta B c i r)) ⊓
                (((P.equal (mul (mul q M) O)) ⊓ (P.equal (mul p M))) ⊓
                  ((mul P (mul uf ui)).equal (add (succ zero) (mul T J))))))))))) := by
  dsimp only
  let M := modulus c i
  let O := modulus c old
  let J := modulus c future
  let B := add b (mul p (mul u (add r (mul (mul (succ i) c) b))))
  let P := mul p M
  let T := add (add vi vf) (mul (mul vf vi) J)
  let R := beta b c old s
  let E := (mul p u).equal (add (succ zero) (mul v M))
  let F := p.equal (mul q O)
  let L := less r M
  let G := (mul p uf).equal (add (succ zero) (mul vf J))
  let I := (mul M ui).equal (add (succ zero) (mul vi J))
  let Γ := [I,G,L,F,E,R]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hr : FOL.Context Peano.Axiom Γ R := .hypothesis (by simp [Γ])
  have he : FOL.Context Peano.Axiom Γ E := .hypothesis (by simp [Γ])
  have hf : FOL.Context Peano.Axiom Γ F := .hypothesis (by simp [Γ])
  have hl : FOL.Context Peano.Axiom Γ L := .hypothesis (by simp [Γ])
  have hg : FOL.Context Peano.Axiom Γ G := .hypothesis (by simp [Γ])
  have hi : FOL.Context Peano.Axiom Γ I := .hypothesis (by simp [Γ])
  have hrows : FOL.Context Peano.Axiom Γ ((beta B c old s) ⊓ (beta B c i r)) :=
    .mp (.mp (.mp (.mp (.closed (PeanoBetaInverseAppend.preserve_and_append
      b p q u v c i old r s)) hr) he) hf) hl
  have hold : FOL.Context Peano.Axiom Γ (P.equal (mul (mul q M) O)) :=
    .mp (.closed (PeanoDivisibility.multiply_preserves_equation p q O M)) hf
  have hnew : FOL.Context Peano.Axiom Γ (P.equal (mul p M)) :=
    .closed (.logical (.eqRefl P))
  have hfuture : FOL.Context Peano.Axiom Γ
      ((mul P (mul uf ui)).equal (add (succ zero) (mul T J))) :=
    .mp (.mp (.closed (PeanoInverseProduct.inverse_product p M uf ui vf vi J)) hg) hi
  exact FOL.Context.conjunctionIntro hrows
    (FOL.Context.conjunctionIntro (FOL.Context.conjunctionIntro hold hnew) hfuture)

end PASoundness.PeanoBetaCRTStep
