import PASoundness.PAtoCompactAllElimVariableInstance
import PASoundness.PAtoCompactScopedActiveDownFull
import PASoundness.PAtoCompactScopedBindVariable
import PASoundness.PAtoCompactVacuousAllElim

/-! Constructive guarded universal elimination for arbitrary variable terms.
The target variable may already occur freely in the source formula. -/
namespace PASoundness.PAtoCompactAllElimVariableFull

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedAllElim
open PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactGuardedAllImp
open PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactVacuousQuantifierFree
open PASoundness.PAtoCompactDirectGeneralization
open PASoundness.PAtoCompactScopedActiveDownFull
open PASoundness.PAtoCompactScopedBindVariable
open PASoundness.PAtoCompactAllElimVariableInstance

set_option maxHeartbeats 0
set_option maxRecDepth 65536

/-- The selected source binder is above the target and source free names.
The resulting active-name alignment allows the target to be already free. -/
noncomputable def variable_scope_alignment (φ : Peano.Formula) (x y : Nat) :
    KBoth (replace (instanceBinder φ x y) y (scopeAt φ x (instanceBinder φ x y)))
      (scopeAt φ x y) := by
  let z := instanceBinder φ x y
  let B := allAtBody x φ
  have htop : topName x φ < z := by
    have hh := ceiling_top φ x
    dsimp [z, instanceBinder]
    omega
  have hfree : z ∉ B.freeVarFinset := by
    intro h
    have hl := free_lt_scopeBase (FOL.allAt x φ) Fin.elim0 z (by
      change z ∈ (allAtBody x φ).freeVarFinset
      exact h)
    change z < topName x φ at hl
    omega
  have hlt : y < z := by dsimp [z, instanceBinder]; omega
  have henv : (rename z y ∘ Fin.snoc Fin.elim0 z) = Fin.snoc Fin.elim0 y := by
    funext i
    fin_cases i
    simp [rename]
  have h := scoped_active_down B (Fin.snoc Fin.elim0 z) (Fin.last 0) y
    (by simpa using hfree) (by simpa using hlt)
  simp only [Fin.snoc_last, henv] at h
  simpa only [scopeAt, B, z, henv] using h

/-- Instantiation and source-level substitution align as finite K proofs. -/
noncomputable def variable_instance (φ : Peano.Formula) (x y : Nat) :
    KDerivation (imp (code (FOL.allAt x φ))
      (imp (domainAt (instanceBinder φ x y + 1) y).encode
        (code (FOL.substAt φ x (.var y))))) := by
  have h := instance_of_low_alignment φ x y (variable_scope_alignment φ x y)
  have hb := (formula_bind_variable φ x y).2
  exact compose h (implicationCongr (identity _) hb)

/-- Every PA universal-elimination axiom with a variable substitution term
has a finite guarded K derivation. No freshness restriction is imposed on y. -/
noncomputable def allElim_variable (φ : Peano.Formula) (x y : Nat) :
    KDerivation (guardedCode (allElimFormula φ x (.var y))) := by
  by_cases hx : x ∈ φ.freeVarFinset
  · let A := allElimFormula φ x (.var y)
    let z := instanceBinder φ x y
    have hmem : y ∈ ((.var y : Peano.Term).varFinset) := by simp
    have hg := termVar_guard φ x (.var y) y hx hmem
    have hlt : y < guardBase A := by
      have hm := termVars_in_axiom_of_occurs φ x (.var y) hx hmem
      have hl : y ≤ A.freeVarFinset.sup id := Finset.le_sup (f := id) hm
      dsimp [guardBase]
      omega
    have hyz : y < z := by dsimp [z, instanceBinder]; omega
    have hd := domainAt_transport (guardBase A) (z+1) y (by omega) (by omega)
    have hi := variable_instance φ x y
    change KDerivation (imp (guardFormula A).encode
      (imp (code (FOL.allAt x φ)) (code (FOL.substAt φ x (.var y)))))
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [code (FOL.allAt x φ), (guardFormula A).encode]
    have hA : Context Γ (code (FOL.allAt x φ)) := Context.head [_] _
    have hG : Context Γ (guardFormula A).encode := .hypothesis (by simp [Γ])
    exact .mp (.mp (.mp hG (.closed hg)) (.closed hd)) (.mp hA (.closed hi))
  · exact PASoundness.PAtoCompactVacuousAllElim.allElim_of_unused φ x (.var y) hx

theorem allElim_variable_certificate (φ : Peano.Formula) (x y : Nat) :
    theoremCode (certificate (allElim_variable φ x y)) =
      guardedCode (allElimFormula φ x (.var y)) := certificate_correct _

end PASoundness.PAtoCompactAllElimVariableFull

#print axioms PASoundness.PAtoCompactAllElimVariableFull.variable_scope_alignment
#print axioms PASoundness.PAtoCompactAllElimVariableFull.variable_instance
#print axioms PASoundness.PAtoCompactAllElimVariableFull.allElim_variable
#print axioms PASoundness.PAtoCompactAllElimVariableFull.allElim_variable_certificate
