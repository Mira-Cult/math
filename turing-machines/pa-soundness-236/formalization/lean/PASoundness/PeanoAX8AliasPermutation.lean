import PASoundness.PeanoFreeNameBinderAction
import PASoundness.PeanoAX8AliasExtraction
import PASoundness.PeanoAX8SingletonFormula

/-! Exact syntax of the alias-case reduction under a finite name permutation. -/
namespace PASoundness.PeanoAX8AliasPermutation
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

/-- Under any swap list sending b to 5 and c to 3, the exact literal alias
reduction becomes the canonical one with the very same permuted decoded
predicate. The existential and universal binders are both transported;
the separate outer b occurrence stays outside the universal. -/
theorem alias_permute (xs : List (Nat × Nat)) (b c : Nat)
    (hb : applyName xs b = 5) (hc : applyName xs c = 3) :
    applyFormula xs (PeanoAX8AliasExtraction.aliasReduced b c) =
      PeanoAX8SingletonFormula.canonicalReduced (applyFormula xs (interpreted c)) := by
  rw [applyFormula_eq, applyFormula_eq]
  change (PeanoAX8AliasExtraction.aliasReduced b c).subst (nameSub (applyName xs)) = _
  unfold PeanoAX8AliasExtraction.aliasReduced PeanoAX8SingletonFormula.canonicalReduced
  rw [existsAt_permute, subst_and, allAt_permute]
  simp [subst_imp, nameSub, hb, hc, bitFormula_subst, FirstOrder.Language.Term.subst]
  rfl

end PASoundness.PeanoAX8AliasPermutation

#print axioms PASoundness.PeanoAX8AliasPermutation.alias_permute
