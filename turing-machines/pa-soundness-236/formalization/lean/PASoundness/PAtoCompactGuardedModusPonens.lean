import PASoundness.PAtoCompactGuardedBridge
import PASoundness.PAtoCompactGuardedEqualityReflexivity
import PASoundness.CompactDerivations

/-! Restricted guarded modus-ponens transformers. When the source formulas
have the same free variables, their guards and the implication guard coincide.
A second result handles inclusion of free-variable sets when the guard bases
agree. The general proof rule remains open: it must also align differing binder
blocks and eliminate additional antecedent-only guards. -/
namespace PASoundness.PAtoCompactGuardedModusPonens

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactHilbertBasis
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedEqualityReflexivity

theorem guard_eq_of_free_eq (φ ψ : Peano.Formula)
    (hf : φ.freeVarFinset = ψ.freeVarFinset) : guardFormula φ = guardFormula ψ := by
  simp [guardFormula, guardBase, hf]

theorem imp_guard_eq_of_free_eq (φ ψ : Peano.Formula)
    (hf : φ.freeVarFinset = ψ.freeVarFinset) :
    guardFormula (φ.imp ψ) = guardFormula ψ := by
  have hf' : (φ.imp ψ).freeVarFinset = ψ.freeVarFinset := by
    simp [BoundedFormula.freeVarFinset, hf]
  exact guard_eq_of_free_eq _ _ hf'

/-- Modus ponens on guarded proof data when both PA formulas have exactly the
same free-variable set. This is not the general guarded proof-rule handler. -/
def same_free_modus_ponens (φ ψ : Peano.Formula)
    (hf : φ.freeVarFinset = ψ.freeVarFinset)
    (di : KDerivation (guardedCode (φ.imp ψ)))
    (da : KDerivation (guardedCode φ)) : KDerivation (guardedCode ψ) := by
  have hg1 := guard_eq_of_free_eq φ ψ hf
  have hg2 := imp_guard_eq_of_free_eq φ ψ hf
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(guardFormula ψ).encode]
  have hG : Context Γ (guardFormula ψ).encode := Context.head [] _
  have hφ : Context Γ (code φ) := by
    apply Context.mp hG
    apply Context.closed
    simpa [guardedCode, hg1] using da
  have hi : Context Γ (imp (code φ) (code ψ)) := by
    apply Context.mp hG
    apply Context.closed
    simpa [guardedCode, hg2, code_imp] using di
  exact Context.mp hφ hi

/-- List inclusion gives a K implication between guard conjunctions when the
private binder block is shared. The lists may be reordered or duplicated. -/
def guardList_subset (base : Nat) (xs ys : List Nat)
    (hs : ∀ x ∈ ys, x ∈ xs) :
    KDerivation (imp (guardList base xs).encode (guardList base ys).encode) := by
  induction ys with
  | nil =>
      simpa [guardList, CompactNamed.Formula.encode] using
        (KDerivation.mp .truth (weakening 0 (guardList base xs).encode))
  | cons y ys ih =>
      apply Context.closeEmpty
      apply Context.deduction
      let Γ := [(guardList base xs).encode]
      have hg : Context Γ (guardList base xs).encode := Context.head [] _
      have hy : Context Γ (domainAt base y).encode :=
        .mp hg (.closed (guardList_projection base y xs (hs y (by simp))))
      have ht : Context Γ (guardList base ys).encode :=
        .mp hg (.closed (ih (by intro x hx; exact hs x (by simp [hx]))))
      have hboth := Context.conjunctionIntro hy ht
      simpa [guardList, andF, CompactNamed.Formula.encode, CompactNamed.Formula.not,
        both, neg] using hboth

/-- If all free variables of the antecedent occur in the consequent and their
guard blocks agree, the consequent guard proves the antecedent guard in K. -/
def guardFormula_subset (φ ψ : Peano.Formula)
    (hs : φ.freeVarFinset ⊆ ψ.freeVarFinset) (hb : guardBase φ = guardBase ψ) :
    KDerivation (imp (guardFormula ψ).encode (guardFormula φ).encode) := by
  unfold guardFormula
  rw [hb]
  apply guardList_subset
  intro x hx
  apply (Finset.mem_sort (· ≤ ·)).mpr
  exact hs ((Finset.mem_sort (· ≤ ·)).mp hx)

/-- A strict-subset extension of the guarded modus-ponens transformer. -/
def subset_same_base_modus_ponens (φ ψ : Peano.Formula)
    (hs : φ.freeVarFinset ⊆ ψ.freeVarFinset) (hb : guardBase φ = guardBase ψ)
    (di : KDerivation (guardedCode (φ.imp ψ)))
    (da : KDerivation (guardedCode φ)) : KDerivation (guardedCode ψ) := by
  have hf : (φ.imp ψ).freeVarFinset = ψ.freeVarFinset := by
    simp only [BoundedFormula.freeVarFinset, Finset.union_eq_right.mpr hs]
  have hi_guard := guard_eq_of_free_eq (φ.imp ψ) ψ hf
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(guardFormula ψ).encode]
  have hg : Context Γ (guardFormula ψ).encode := Context.head [] _
  have ha_guard : Context Γ (guardFormula φ).encode :=
    .mp hg (.closed (guardFormula_subset φ ψ hs hb))
  have ha : Context Γ (code φ) := .mp ha_guard (.closed da)
  have hi : Context Γ (imp (code φ) (code ψ)) := by
    apply Context.mp hg
    apply Context.closed
    simpa [guardedCode, hi_guard, code_imp] using di
  exact .mp ha hi

end PASoundness.PAtoCompactGuardedModusPonens

#print axioms PASoundness.PAtoCompactGuardedModusPonens.guard_eq_of_free_eq
#print axioms PASoundness.PAtoCompactGuardedModusPonens.imp_guard_eq_of_free_eq
#print axioms PASoundness.PAtoCompactGuardedModusPonens.same_free_modus_ponens
#print axioms PASoundness.PAtoCompactGuardedModusPonens.guardList_subset
#print axioms PASoundness.PAtoCompactGuardedModusPonens.guardFormula_subset
#print axioms PASoundness.PAtoCompactGuardedModusPonens.subset_same_base_modus_ponens
