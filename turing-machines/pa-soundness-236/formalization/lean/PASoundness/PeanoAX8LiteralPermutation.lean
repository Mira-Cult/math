import PASoundness.PeanoFreeNameBinderAction
import PASoundness.PeanoAX8CanonicalFormula

/-! Exact transport of a literal distinct-name AX8 formula to its canonical
names. This is a syntax identity, not an AX8 derivation. -/
namespace PASoundness.PeanoAX8LiteralPermutation
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic CompactLogicalTransport
open PeanoFreeNamePermutation PeanoFreeNameBinderAction

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl

private theorem subst_and (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  rw [subst_not]
  rfl

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

/-- A free-name permutation that maps a,b,c to 4,5,3 respectively carries
the literal comprehension formula to the exact canonical formula. The
same b is bound in the universal clause and free in the outer clause; the
injective binder-action identities preserve that distinction. -/
theorem literal_permutation (xs : List (Nat × Nat)) (a b c : Nat)
    (ha : applyName xs a = 4) (hb : applyName xs b = 5)
    (hc : applyName xs c = 3) :
    applyFormula xs (comprehensionFormula a b c) =
      PeanoAX8CanonicalFormula.canonicalFormula (applyFormula xs (interpreted c)) := by
  rw [applyFormula_eq, applyFormula_eq]
  let σ := nameSub (applyName xs)
  change (comprehensionFormula a b c).subst σ =
    PeanoAX8CanonicalFormula.canonicalFormula ((interpreted c).subst σ)
  change (FOL.existsAt c
    ((FOL.allAt b (((bitFormula (.var a) (.var b)).imp
      ((interpreted c).imp (bitFormula (.var c) (.var b)))) ⊓
      ((bitFormula (.var c) (.var b)).imp (interpreted c)))) ⊓
      ((interpreted c).imp (bitFormula (.var c) (.var b))))).subst σ = _
  unfold PeanoAX8CanonicalFormula.canonicalFormula
  rw [existsAt_permute]
  simp only [subst_and, subst_imp, allAt_permute, bitFormula_subst,
    FirstOrder.Language.Term.subst, nameSub, ha, hb, hc]
  rfl

end PASoundness.PeanoAX8LiteralPermutation

#print axioms PASoundness.PeanoAX8LiteralPermutation.literal_permutation
