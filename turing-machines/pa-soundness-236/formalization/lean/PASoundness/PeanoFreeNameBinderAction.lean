import PASoundness.PeanoFreeNamePermutationInverse
import PASoundness.PeanoBetaCRTPrefixSubst

/-! Exact action of an injective free-name renaming on named binders.
These are finite syntax identities, not semantic or comprehension results. -/
namespace PASoundness.PeanoFreeNameBinderAction
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic
open PeanoBetaCRTPrefixSubst.Syntax

def nameSub (f : Nat → Nat) : Nat → Peano.Term := fun z => .var (f z)

private theorem term_bind_rename (f : Nat → Nat) (hf : Function.Injective f)
    (x n : Nat) (t : Peano.language.Term (Nat ⊕ Fin n)) :
    (t.relabel (BoundedFormula.relabelAux (bindName x) n)).subst
      (SyntaxTransport.liftSub (1+n) (nameSub f)) =
    (t.subst (SyntaxTransport.liftSub n (nameSub f))).relabel
      (BoundedFormula.relabelAux (bindName (f x)) n) := by
  rw [SyntaxTransport.term_relabel_subst, SyntaxTransport.term_subst_relabel]
  congr 1
  funext z
  cases z with
  | inl z =>
    by_cases hz : z = x
    · subst z
      simp [BoundedFormula.relabelAux, bindName, SyntaxTransport.liftSub, nameSub,
        FirstOrder.Language.Term.relabel]
    · have hfx : f z ≠ f x := fun h => hz (hf h)
      simp [BoundedFormula.relabelAux, bindName, SyntaxTransport.liftSub, nameSub,
        FirstOrder.Language.Term.relabel, hz, hfx]
  | inr z =>
    simp [BoundedFormula.relabelAux, SyntaxTransport.liftSub,
      FirstOrder.Language.Term.relabel]

private theorem bounded_bind_rename {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (f : Nat → Nat) (hf : Function.Injective f) (x : Nat) :
    (φ.relabel (bindName x)).subst (nameSub f) =
      (φ.subst (nameSub f)).relabel (bindName (f x)) := by
  induction φ with
  | falsum => rfl
  | equal t u =>
    change BoundedFormula.equal
      ((t.relabel (BoundedFormula.relabelAux (bindName x) _)).subst
        (SyntaxTransport.liftSub _ (nameSub f)))
      ((u.relabel (BoundedFormula.relabelAux (bindName x) _)).subst
        (SyntaxTransport.liftSub _ (nameSub f))) =
      BoundedFormula.equal
      ((t.subst (SyntaxTransport.liftSub _ (nameSub f))).relabel
        (BoundedFormula.relabelAux (bindName (f x)) _))
      ((u.subst (SyntaxTransport.liftSub _ (nameSub f))).relabel
        (BoundedFormula.relabelAux (bindName (f x)) _))
    rw [term_bind_rename f hf x _ t, term_bind_rename f hf x _ u]
  | rel rel ts =>
    change BoundedFormula.rel rel (fun i =>
      ((ts i).relabel (BoundedFormula.relabelAux (bindName x) _)).subst
        (SyntaxTransport.liftSub _ (nameSub f))) =
      BoundedFormula.rel rel (fun i =>
        ((ts i).subst (SyntaxTransport.liftSub _ (nameSub f))).relabel
          (BoundedFormula.relabelAux (bindName (f x)) _))
    congr 1
    funext i
    exact term_bind_rename f hf x _ (ts i)
  | imp a b ia ib =>
    simpa only [BoundedFormula.relabel_imp, BoundedFormula.subst,
      BoundedFormula.mapTermRel] using congrArg₂ BoundedFormula.imp ia ib
  | all g ih =>
    simpa only [BoundedFormula.relabel_all, BoundedFormula.subst,
      BoundedFormula.mapTermRel, id_eq] using congrArg BoundedFormula.all ih

/-- Injective free-name renaming carries an `allAt x` binder to `allAt (f x)`
and renames its body consistently, including nested bound variables. -/
theorem allAt_rename (φ : Peano.Formula) (f : Nat → Nat)
    (hf : Function.Injective f) (x : Nat) :
    (FOL.allAt x φ).subst (nameSub f) = FOL.allAt (f x) (φ.subst (nameSub f)) := by
  unfold FOL.allAt
  change ((BoundedFormula.relabel (bindName x) φ).subst (nameSub f)).all =
    (BoundedFormula.relabel (bindName (f x)) (φ.subst (nameSub f))).all
  exact congrArg BoundedFormula.all (bounded_bind_rename φ f hf x)

/-- Existential counterpart of the same exact binder action. -/
theorem existsAt_rename (φ : Peano.Formula) (f : Nat → Nat)
    (hf : Function.Injective f) (x : Nat) :
    (FOL.existsAt x φ).subst (nameSub f) = FOL.existsAt (f x) (φ.subst (nameSub f)) := by
  unfold FOL.existsAt
  change ((FOL.allAt x φ.not).subst (nameSub f)).not =
    (FOL.allAt (f x) (φ.subst (nameSub f)).not).not
  apply congrArg BoundedFormula.not
  rw [allAt_rename φ.not f hf x]
  congr 1

/-- The above applies directly to any finite sequence of swaps. -/
theorem allAt_permute (φ : Peano.Formula) (xs : List (Nat × Nat)) (x : Nat) :
    (FOL.allAt x φ).subst (nameSub (PeanoFreeNamePermutation.applyName xs)) =
      FOL.allAt (PeanoFreeNamePermutation.applyName xs x)
        (φ.subst (nameSub (PeanoFreeNamePermutation.applyName xs))) :=
  allAt_rename φ _ (PeanoFreeNamePermutationInverse.applyName_injective xs) x

theorem existsAt_permute (φ : Peano.Formula) (xs : List (Nat × Nat)) (x : Nat) :
    (FOL.existsAt x φ).subst (nameSub (PeanoFreeNamePermutation.applyName xs)) =
      FOL.existsAt (PeanoFreeNamePermutation.applyName xs x)
        (φ.subst (nameSub (PeanoFreeNamePermutation.applyName xs))) :=
  existsAt_rename φ _ (PeanoFreeNamePermutationInverse.applyName_injective xs) x

end PASoundness.PeanoFreeNameBinderAction

#print axioms PASoundness.PeanoFreeNameBinderAction.allAt_permute
#print axioms PASoundness.PeanoFreeNameBinderAction.existsAt_permute
