import PASoundness.PAtoCompactGuardedModusPonensTransport
import PASoundness.PAtoCompactGuardElimination
import PASoundness.PAtoCompactGuardedVacuity
import PASoundness.PAtoCompactGuardAssembly
import PASoundness.PAtoCompactGuardedPropositional

/-! Guard elimination for the guarded modus-ponens proof. -/
namespace PASoundness.PAtoCompactGuardedModusPonensFull

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedVacuity
open PASoundness.PAtoCompactGuardedEqualityReflexivity PASoundness.PAtoCompactGuardedModusPonens
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactGuardedModusPonensTransport
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactGuardElimination
open PASoundness.PAtoCompactGuardAssembly

/-- Eliminate finitely many candidate guards which are fresh in the conclusion. -/
def remove_extras (ψ : Peano.Formula) (base : Nat) (xs : List Nat)
    (hn : xs.Nodup) (hf : ∀ x ∈ xs, x ∉ ψ.freeVarFinset)
    (hb : ∀ x ∈ xs, x < base + 2)
    (d : KDerivation (imp (guardFormula ψ).encode
      (imp (guardList base xs).encode (code ψ)))) : KDerivation (guardedCode ψ) := by
  induction xs with
  | nil =>
      apply Context.closeEmpty
      apply Context.deduction
      have hg := Context.head [] (guardFormula ψ).encode
      have hd := Context.mp hg (.closed d)
      exact Context.mp (.closed .truth) hd
  | cons x xs ih =>
      have hnod : x ∉ xs ∧ xs.Nodup := List.nodup_cons.mp hn
      have hxf : x ∉ ψ.freeVarFinset := hf x (by simp)
      have hvG := guardFormula_vacuity ψ x hxf
      have hvB : KDerivation (imp (imp (guardList base xs).encode (code ψ))
          (allCode x (imp (guardList base xs).encode (code ψ)))) := by
        apply free_vacuity x (Formula.imp (guardList base xs) (formula ψ))
        simp only [Formula.free, Finset.mem_union, not_or]
        constructor
        · intro h
          exact hnod.1 (List.mem_toFinset.mp (guardList_free_subset base xs h))
        · intro h
          exact hxf (formula_free_subset ψ h)
      have hr : KDerivation (imp (guardFormula ψ).encode
          (imp (domainAt base x).encode (imp (guardList base xs).encode (code ψ)))) := by
        apply Context.closeEmpty
        apply Context.deduction
        apply Context.deduction
        apply Context.deduction
        let Γ := [(guardList base xs).encode, (domainAt base x).encode, (guardFormula ψ).encode]
        have hg : Context Γ (guardFormula ψ).encode := .hypothesis (by simp [Γ])
        have hx : Context Γ (domainAt base x).encode := .hypothesis (by simp [Γ])
        have ht : Context Γ (guardList base xs).encode := .hypothesis (by simp [Γ])
        have hc : Context Γ (guardList base (x :: xs)).encode := by
          have hh := Context.conjunctionIntro hx ht
          simpa [guardList, andF, CompactNamed.Formula.encode, CompactNamed.Formula.not, both, neg] using hh
        exact .mp hc (.mp hg (.closed d))
      have hdrop := eliminate_fresh_candidate x base (guardFormula ψ).encode
        (imp (guardList base xs).encode (code ψ)) (hb x (by simp)) hvG hvB hr
      exact ih hnod.2 (by intro y hy; exact hf y (by simp [hy]))
        (by intro y hy; exact hb y (by simp [hy])) hdrop

def extraList (φ ψ : Peano.Formula) : List Nat :=
  (φ.freeVarFinset \ ψ.freeVarFinset).sort (· ≤ ·)

/-- Assemble any guard supported on the two source free-variable sets. -/
def assemble_guard (φ ψ τ : Peano.Formula)
    (ht : τ.freeVarFinset ⊆ φ.freeVarFinset ∪ ψ.freeVarFinset) :
    KDerivation (imp (guardFormula ψ).encode
      (imp (guardList (guardBase (φ.imp ψ)) (extraList φ ψ)).encode
        (guardFormula τ).encode)) := by
  unfold guardFormula
  apply guardList_combine
  · intro x hx
    have hx' := (Finset.mem_sort (· ≤ ·)).mp hx
    have hle : x ≤ ψ.freeVarFinset.sup id := Finset.le_sup (f := id) hx'
    unfold guardBase
    omega
  · intro x hx
    have hx' : x ∈ φ.freeVarFinset ∪ ψ.freeVarFinset := by
      have hh := (Finset.mem_sort (· ≤ ·)).mp hx
      exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hh).1
    have hle : x ≤ (φ.imp ψ).freeVarFinset.sup id := by
      apply Finset.le_sup (f := id)
      simpa [BoundedFormula.freeVarFinset] using hx'
    unfold guardBase
    omega
  · intro x hx
    have hx' := (Finset.mem_sort (· ≤ ·)).mp hx
    have hle : x ≤ τ.freeVarFinset.sup id := Finset.le_sup (f := id) hx'
    unfold guardBase
    omega
  · intro x hx
    have hxτ := (Finset.mem_sort (· ≤ ·)).mp hx
    have hxunion := ht hxτ
    by_cases hxψ : x ∈ ψ.freeVarFinset
    · exact Or.inl ((Finset.mem_sort (· ≤ ·)).mpr hxψ)
    · right
      apply (Finset.mem_sort (· ≤ ·)).mpr
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_union.mp hxunion).resolve_right hxψ, hxψ⟩

/-- Unrestricted modus ponens for the guarded PA translation, as an actual
transformer of finite K proof data. -/
def modusPonens (φ ψ : Peano.Formula)
    (di : KDerivation (guardedCode (φ.imp ψ)))
    (da : KDerivation (guardedCode φ)) : KDerivation (guardedCode ψ) := by
  apply remove_extras ψ (guardBase (φ.imp ψ)) (extraList φ ψ)
  · exact Finset.sort_nodup _ _
  · intro x hx
    have h := (Finset.mem_sort (· ≤ ·)).mp hx
    exact (Finset.mem_sdiff.mp h).2
  · intro x hx
    have h := (Finset.mem_sort (· ≤ ·)).mp hx
    have hf : x ∈ (φ.imp ψ).freeVarFinset := by
      simpa [BoundedFormula.freeVarFinset] using
        (Finset.mem_union_left ψ.freeVarFinset (Finset.mem_sdiff.mp h).1)
    have hle : x ≤ (φ.imp ψ).freeVarFinset.sup id := Finset.le_sup (f := id) hf
    unfold guardBase
    omega
  · have hφ := assemble_guard φ ψ φ (Finset.subset_union_left)
    have hi := assemble_guard φ ψ (φ.imp ψ) (by simp [BoundedFormula.freeVarFinset])
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(guardList (guardBase (φ.imp ψ)) (extraList φ ψ)).encode,
      (guardFormula ψ).encode]
    have hg : Context Γ (guardFormula ψ).encode := .hypothesis (by simp [Γ])
    have he : Context Γ (guardList (guardBase (φ.imp ψ)) (extraList φ ψ)).encode :=
      .hypothesis (by simp [Γ])
    have ha_guard : Context Γ (guardFormula φ).encode := .mp he (.mp hg (.closed hφ))
    have hi_guard : Context Γ (guardFormula (φ.imp ψ)).encode := .mp he (.mp hg (.closed hi))
    have ha : Context Γ (code φ) := .mp ha_guard (.closed da)
    have hi' : Context Γ (imp (code φ) (code ψ)) := by
      apply Context.mp hi_guard
      apply Context.closed
      simpa [guardedCode, code_imp] using di
    exact .mp ha hi'

theorem modusPonens_certificate (φ ψ : Peano.Formula)
    (di : KDerivation (guardedCode (φ.imp ψ)))
    (da : KDerivation (guardedCode φ)) :
    theoremCode (certificate (modusPonens φ ψ di da)) = guardedCode ψ :=
  certificate_correct _

/-- Build the guarded compiler's handlers with modus ponens discharged.
The five nonpropositional logical families, PA axioms and generalization
remain explicit finite-proof obligations. -/
def handlers (logical : PAtoCompactGuardedPropositional.RemainingLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ))
    (generalization : ∀ x φ, KDerivation (guardedCode φ) →
      KDerivation (guardedCode (FOL.allAt x φ))) : PAtoCompactGuardedBridge.Handlers :=
  PAtoCompactGuardedPropositional.guardedHandlers logical arithmetic modusPonens generalization

end PASoundness.PAtoCompactGuardedModusPonensFull

#print axioms PASoundness.PAtoCompactGuardedModusPonensFull.remove_extras
#print axioms PASoundness.PAtoCompactGuardedModusPonensFull.assemble_guard
#print axioms PASoundness.PAtoCompactGuardedModusPonensFull.modusPonens
#print axioms PASoundness.PAtoCompactGuardedModusPonensFull.modusPonens_certificate
#print axioms PASoundness.PAtoCompactGuardedModusPonensFull.handlers
