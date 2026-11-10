import PASoundness.PeanoBetaPairInverse
import PASoundness.PeanoBetaInverseAppend

/-! A concrete two-row beta-code update, proved inside PA. This establishes a
fixed pair only; bounded-family preservation and power-trace extension remain
separate obligations. -/
namespace PASoundness.PeanoBetaPairUpdate
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic
open PeanoBetaPairInverse

/-- For the parameter `(S k)*(S h)`, construct one new beta code preserving
the existing row at `i` while installing the bounded value `r` at `i+S k`.
All arithmetic is object-level PA; the only antecedents are the existing row
and the bound for the desired new row. -/
theorem update_two_rows (b i k h r s : Peano.Term) :
    let K := succ k
    let H := succ h
    let C := mul K H
    let J := add i K
    let A := succ i
    let P := mul (mul A A) H
    let T := mul K C
    let D := triplePred i k h
    let U := mul (add D P) (succ (add D T))
    let M := modulus C i
    let B := add b (mul M (mul U (add r (mul (mul (succ J) C) b))))
    FormulaProves ((beta b C i s).imp ((less r (modulus C J)).imp
      ((beta B C i s) ⊓ (beta B C J r)))) := by
  dsimp only
  let K := succ k
  let H := succ h
  let C := mul K H
  let J := add i K
  let A := succ i
  let P := mul (mul A A) H
  let T := mul K C
  let D := triplePred i k h
  let E := triplePred i i h
  let U := mul (add D P) (succ (add D T))
  let V := add (add D T) (mul E (succ (add D T)))
  let M := modulus C i
  let B := add b (mul M (mul U (add r (mul (mul (succ J) C) b))))
  let R := beta b C i s
  let L := less r (modulus C J)
  let Γ := [L,R]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hr : FOL.Context Peano.Axiom Γ R := FOL.Context.under (FOL.Context.head [] R) L
  have hl : FOL.Context Peano.Axiom Γ L := FOL.Context.head _ _
  have hi : FOL.Context Peano.Axiom Γ ((mul M U).equal
      (add (succ zero) (mul V (modulus C J)))) :=
    .closed (beta_modulus_pair_inverse_positive i k h)
  have hd : FOL.Context Peano.Axiom Γ (M.equal (mul (succ zero) (modulus C i))) :=
    .closed (FOL.Derivation.eqSymm (PeanoArithmetic.one_mul M))
  have hm := PeanoBetaInverseAppend.preserve_and_append b M (succ zero) U V C J i r s
  exact .mp (.mp (.mp (.mp (.closed hm) hr) hi) hd) hl

end PASoundness.PeanoBetaPairUpdate
