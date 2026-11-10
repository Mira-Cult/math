import PASoundness.PAtoCompactGuardedModusPonens
import PASoundness.PAtoCompactGuardBaseTransport

/-! Guarded modus ponens when every antecedent free variable occurs in the
consequent. Candidate guards are transported between independently chosen
private binder blocks. The general rule, which must eliminate antecedent-only
guards, remains open. -/
namespace PASoundness.PAtoCompactGuardedModusPonensTransport

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactHilbertBasis
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedEqualityReflexivity
open PASoundness.PAtoCompactGuardedModusPonens PASoundness.PAtoCompactGuardBaseTransport

/-- Finite K guard-list transport along inclusion and independently selected
private binder blocks. The two freshness bounds apply to each target name. -/
def guardList_transport_subset (b c : Nat) (xs ys : List Nat)
    (hs : ∀ x ∈ ys, x ∈ xs)
    (hb : ∀ x ∈ ys, x < b + 32) (hc : ∀ x ∈ ys, x < c + 32) :
    KDerivation (imp (guardList b xs).encode (guardList c ys).encode) := by
  induction ys with
  | nil =>
      simpa [guardList, CompactNamed.Formula.encode] using
        (KDerivation.mp .truth (weakening 0 (guardList b xs).encode))
  | cons y ys ih =>
      apply Context.closeEmpty
      apply Context.deduction
      let Γ := [(guardList b xs).encode]
      have hg : Context Γ (guardList b xs).encode := Context.head [] _
      have hyb : Context Γ (domainAt b y).encode :=
        .mp hg (.closed (guardList_projection b y xs (hs y (by simp))))
      have hyc : Context Γ (domainAt c y).encode :=
        .mp hyb (.closed (domainAt_transport b c y (hb y (by simp)) (hc y (by simp))))
      have ht : Context Γ (guardList c ys).encode :=
        .mp hg (.closed (ih (by intro x hx; exact hs x (by simp [hx]))
          (by intro x hx; exact hb x (by simp [hx]))
          (by intro x hx; exact hc x (by simp [hx]))))
      have hboth := Context.conjunctionIntro hyc ht
      simpa [guardList, andF, CompactNamed.Formula.encode, CompactNamed.Formula.not,
        both, neg] using hboth

/-- Under free-variable inclusion, the consequent guard proves the
antecedent guard, with no equality requirement on their private blocks. -/
def guardFormula_transport_subset (φ ψ : Peano.Formula)
    (hs : φ.freeVarFinset ⊆ ψ.freeVarFinset) :
    KDerivation (imp (guardFormula ψ).encode (guardFormula φ).encode) := by
  unfold guardFormula
  apply guardList_transport_subset
  · intro x hx
    apply (Finset.mem_sort (· ≤ ·)).mpr
    exact hs ((Finset.mem_sort (· ≤ ·)).mp hx)
  · intro x hx
    have hxφ := (Finset.mem_sort (· ≤ ·)).mp hx
    have hle : x ≤ ψ.freeVarFinset.sup id := Finset.le_sup (f := id) (hs hxφ)
    unfold guardBase
    omega
  · intro x hx
    have hxφ := (Finset.mem_sort (· ≤ ·)).mp hx
    have hle : x ≤ φ.freeVarFinset.sup id := Finset.le_sup (f := id) hxφ
    unfold guardBase
    omega

/-- Guarded modus ponens when the antecedent's free variables are all free in
the consequent. It produces finite K proof data from the two input proofs. -/
def subset_modus_ponens (φ ψ : Peano.Formula)
    (hs : φ.freeVarFinset ⊆ ψ.freeVarFinset)
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
    .mp hg (.closed (guardFormula_transport_subset φ ψ hs))
  have ha : Context Γ (code φ) := .mp ha_guard (.closed da)
  have hi : Context Γ (imp (code φ) (code ψ)) := by
    apply Context.mp hg
    apply Context.closed
    simpa [guardedCode, hi_guard, code_imp] using di
  exact .mp ha hi

end PASoundness.PAtoCompactGuardedModusPonensTransport

#print axioms PASoundness.PAtoCompactGuardedModusPonensTransport.guardList_transport_subset
#print axioms PASoundness.PAtoCompactGuardedModusPonensTransport.guardFormula_transport_subset
#print axioms PASoundness.PAtoCompactGuardedModusPonensTransport.subset_modus_ponens
