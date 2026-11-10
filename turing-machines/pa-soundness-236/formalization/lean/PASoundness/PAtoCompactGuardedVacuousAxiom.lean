import PASoundness.PAtoCompactGuardedGeneralizationAlignment
import PASoundness.PAtoCompactGuardedPropositional
import PASoundness.PAtoCompactFreeVacuity

/-! Conditional reduction of the guarded PA vacuous logical axiom to the
actual generated-body alignment. The alignment is explicit K proof data;
this file does not construct it or claim the full logical handler. -/
namespace PASoundness.PAtoCompactGuardedVacuousAxiom

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedPropositional
open PASoundness.PAtoCompactGuardedGeneralizationAlignment

/-- With an unused source variable, the new top binder is fresh in the
original source formula. -/
theorem topName_not_free (φ : Peano.Formula) (x : Nat)
    (hx : x ∉ φ.freeVarFinset) : topName x φ ∉ φ.freeVarFinset := by
  intro hz
  have h : topName x φ ∈ (FOL.allAt x φ).freeVarFinset := by
    simpa [PASoundness.SyntaxTransport.allAt_freeVars, hx] using hz
  have hl := free_lt_scopeBase (FOL.allAt x φ) Fin.elim0 (topName x φ) h
  exact Nat.lt_irrefl _ hl

/-- For an unused source variable, a K proof that the original translation
implies the actual generated body yields the guarded vacuous-axiom proof. -/
def vacuous_of_body_alignment (φ : Peano.Formula) (x : Nat)
    (hx : x ∉ φ.freeVarFinset)
    (halign : KDerivation (imp (code φ) (topBody x φ).encode)) :
    KDerivation (guardedCode (φ.imp (FOL.allAt x φ))) := by
  apply guardedOfUnconditional
  rw [code_imp, code_allAt]
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [code φ]
  have hp : Context Γ (code φ) := Context.head [] _
  apply generalizeOne (topName x φ) (translated_vacuity φ (topName x φ) (topName_not_free φ x hx))
  apply Context.mp hp
  apply Context.closed
  exact compose halign (weakening _ _)

theorem vacuous_of_body_alignment_certificate (φ : Peano.Formula) (x : Nat)
    (hx : x ∉ φ.freeVarFinset)
    (halign : KDerivation (imp (code φ) (topBody x φ).encode)) :
    theoremCode (certificate (vacuous_of_body_alignment φ x hx halign)) =
      guardedCode (φ.imp (FOL.allAt x φ)) := certificate_correct _

/-- The falsum instance has identical generated bodies and needs no
alignment assumption. -/
def falsum_instance (x : Nat) :
    KDerivation (guardedCode ((.falsum : Peano.Formula).imp
      (FOL.allAt x (.falsum : Peano.Formula)))) := by
  apply vacuous_of_body_alignment
  · simp [BoundedFormula.freeVarFinset]
  · change KDerivation (imp 1 1)
    exact identity 1

theorem falsum_instance_certificate (x : Nat) :
    theoremCode (certificate (falsum_instance x)) =
      guardedCode ((.falsum : Peano.Formula).imp (FOL.allAt x .falsum)) :=
  certificate_correct _

end PASoundness.PAtoCompactGuardedVacuousAxiom

#print axioms PASoundness.PAtoCompactGuardedVacuousAxiom.topName_not_free
#print axioms PASoundness.PAtoCompactGuardedVacuousAxiom.vacuous_of_body_alignment
#print axioms PASoundness.PAtoCompactGuardedVacuousAxiom.vacuous_of_body_alignment_certificate
#print axioms PASoundness.PAtoCompactGuardedVacuousAxiom.falsum_instance
#print axioms PASoundness.PAtoCompactGuardedVacuousAxiom.falsum_instance_certificate
