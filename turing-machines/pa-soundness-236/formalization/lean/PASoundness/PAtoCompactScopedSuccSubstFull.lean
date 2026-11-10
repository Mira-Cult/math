import PASoundness.PAtoCompactGuardedLogicalCongruence
import PASoundness.PAtoCompactFormulaTranslation
import PASoundness.CompactDerivations
import PASoundness.PAtoCompactScopedSuccSubstUniversal

/-! Induction through bounded PA syntax while retaining a single hypothesis.
Equality leaves are explicit finite-K inputs. -/
namespace PASoundness.PAtoCompactScopedSuccSubstFull

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedLogicalCongruence

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- Only actual equality leaves require alignment. Each leaf must hold for
every active-name environment, allowing free and bound labels to alias. -/
inductive ScopedLeaves (H : Formula) (σ τ : Nat → Peano.Term) :
    {n : Nat} → Peano.language.BoundedFormula Nat n → Type
  | falsum {n : Nat} : ScopedLeaves H σ τ (.falsum : Peano.language.BoundedFormula Nat n)
  | equal {n : Nat} (s t : Peano.language.Term (Nat ⊕ Fin n)) :
      (∀ bound : Fin n → Nat,
        GuardedBoth H (scopedFormula n ((.equal s t : Peano.language.BoundedFormula Nat n).subst σ) bound)
          (scopedFormula n ((.equal s t : Peano.language.BoundedFormula Nat n).subst τ) bound)) →
      ScopedLeaves H σ τ (.equal s t)
  | imp {n : Nat} {a b : Peano.language.BoundedFormula Nat n} :
      ScopedLeaves H σ τ a → ScopedLeaves H σ τ b → ScopedLeaves H σ τ (.imp a b)
  | all {n : Nat} {body : Peano.language.BoundedFormula Nat (n+1)} :
      ScopedLeaves H σ τ body → ScopedLeaves H σ τ (.all body)

/-- A guarded universal step whose body induction hypothesis works at every
active-name environment. No source-model or semantic argument is assumed. -/
abbrev UniversalStep (H : Formula) (σ τ : Nat → Peano.Term) :=
  ∀ (n : Nat) (body : Peano.language.BoundedFormula Nat (n+1)),
    (∀ bound : Fin (n+1) → Nat,
      GuardedBoth H (scopedFormula (n+1) (body.subst σ) bound)
        (scopedFormula (n+1) (body.subst τ) bound)) →
    ∀ bound : Fin n → Nat,
      GuardedBoth H (scopedFormula n ((.all body : Peano.language.BoundedFormula Nat n).subst σ) bound)
        (scopedFormula n ((.all body : Peano.language.BoundedFormula Nat n).subst τ) bound)

/-- Lift precisely the supplied atom alignments through the whole formula. -/
noncomputable def scoped_substitution_of_universal (H : Formula) (σ τ : Nat → Peano.Term)
    (universal : UniversalStep H σ τ) {n : Nat}
    {φ : Peano.language.BoundedFormula Nat n} (leaves : ScopedLeaves H σ τ φ) :
    ∀ bound : Fin n → Nat,
      GuardedBoth H (scopedFormula n (φ.subst σ) bound) (scopedFormula n (φ.subst τ) bound) := by
  induction leaves with
  | falsum =>
      intro bound
      constructor <;> apply Context.closeEmpty <;> apply Context.deduction <;>
        exact .closed (identity _)
  | equal s t h => exact h
  | @imp n a b la lb ia ib =>
      intro bound
      change GuardedBoth H
        (.imp (scopedFormula _ (a.subst σ) bound) (scopedFormula _ (b.subst σ) bound))
        (.imp (scopedFormula _ (a.subst τ) bound) (scopedFormula _ (b.subst τ) bound))
      exact guarded_implication _ _ _ _ _ (ia bound) (ib bound)
  | @all n body leaves ih => exact universal n body ih

/-- Both guarded directions for arbitrary nested formulas. Only the actual
equality leaves are inputs; the universal step is constructed syntactically. -/
noncomputable def scoped_substitution (H : Formula) (σ τ : Nat → Peano.Term)
    {n : Nat} {φ : Peano.language.BoundedFormula Nat n} (leaves : ScopedLeaves H σ τ φ) :
    ∀ bound : Fin n → Nat,
      GuardedBoth H (scopedFormula n (φ.subst σ) bound) (scopedFormula n (φ.subst τ) bound) := by
  apply scoped_substitution_of_universal H σ τ
  · intro n body ih bound
    exact PASoundness.PAtoCompactScopedSuccSubstUniversal.universal_step body σ τ H ih bound
  · exact leaves

theorem scoped_substitution_forward_certificate (H : Formula) (σ τ : Nat → Peano.Term)
    {n : Nat} {φ : Peano.language.BoundedFormula Nat n} (leaves : ScopedLeaves H σ τ φ)
    (bound : Fin n → Nat) :
    theoremCode (certificate ((scoped_substitution H σ τ leaves bound).1)) =
      imp H.encode (imp (scopedFormula n (φ.subst σ) bound).encode
        (scopedFormula n (φ.subst τ) bound).encode) := certificate_correct _

theorem scoped_substitution_backward_certificate (H : Formula) (σ τ : Nat → Peano.Term)
    {n : Nat} {φ : Peano.language.BoundedFormula Nat n} (leaves : ScopedLeaves H σ τ φ)
    (bound : Fin n → Nat) :
    theoremCode (certificate ((scoped_substitution H σ τ leaves bound).2)) =
      imp H.encode (imp (scopedFormula n (φ.subst τ) bound).encode
        (scopedFormula n (φ.subst σ) bound).encode) := certificate_correct _

end PASoundness.PAtoCompactScopedSuccSubstFull

#print axioms PASoundness.PAtoCompactScopedSuccSubstFull.scoped_substitution_of_universal
#print axioms PASoundness.PAtoCompactScopedSuccSubstFull.scoped_substitution
#print axioms PASoundness.PAtoCompactScopedSuccSubstFull.scoped_substitution_forward_certificate
#print axioms PASoundness.PAtoCompactScopedSuccSubstFull.scoped_substitution_backward_certificate
