import PASoundness.PAtoCompactGuardedBridge
import PASoundness.PAtoCompactPropositionalHandlers

/-! Finite K proof data for the propositional leaves of the guarded PA
translation. Quantifier and equality leaves, PA axioms, and proof rules remain
explicit obligations. -/
namespace PASoundness.PAtoCompactGuardedPropositional

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactPropositionalHandlers

/-- A finite K proof remains a proof after adding the formula's guard. -/
def guardedOfUnconditional (φ : Peano.Formula) (d : KDerivation (code φ)) :
    KDerivation (guardedCode φ) :=
  .mp d (weakening (code φ) (guardFormula φ).encode)

def translated_k (φ ψ : Peano.Formula) :
    KDerivation (guardedCode (φ.imp (ψ.imp φ))) :=
  guardedOfUnconditional _ (PAtoCompactPropositionalHandlers.translated_k φ ψ)

def translated_s (φ ψ χ : Peano.Formula) :
    KDerivation (guardedCode ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))) :=
  guardedOfUnconditional _ (PAtoCompactPropositionalHandlers.translated_s φ ψ χ)

def translated_classical (φ : Peano.Formula) :
    KDerivation (guardedCode (φ.not.not.imp φ)) :=
  guardedOfUnconditional _ (PAtoCompactPropositionalHandlers.translated_classical φ)

/-- The five nonpropositional logical leaves still require finite K proofs. -/
structure RemainingLogical where
  allElim : ∀ (φ : Peano.Formula) (x : Nat) (t : Peano.Term),
    KDerivation (guardedCode ((FOL.allAt x φ).imp (FOL.substAt φ x t)))
  allImp : ∀ (φ ψ : Peano.Formula) (x : Nat),
    KDerivation (guardedCode ((FOL.allAt x (φ.imp ψ)).imp
      ((FOL.allAt x φ).imp (FOL.allAt x ψ))))
  vacuous : ∀ (φ : Peano.Formula) (x : Nat), x ∉ φ.freeVarFinset →
    KDerivation (guardedCode (φ.imp (FOL.allAt x φ)))
  eqRefl : ∀ (t : Peano.Term), KDerivation (guardedCode (t.equal t))
  eqSubst : ∀ (φ : Peano.Formula) (x : Nat) (t u : Peano.Term),
    KDerivation (guardedCode ((t.equal u).imp ((FOL.substAt φ x t).imp (FOL.substAt φ x u))))

/-- Dispatch every checked logical leaf, with the remaining families explicit. -/
def logicalHandler (h : RemainingLogical) (c : Certificates.LogicalCode Peano.language)
    (φ : Peano.Formula) (hc : Certificates.logicalDecode c = some φ) :
    KDerivation (guardedCode φ) := by
  cases c with
  | k a b =>
      cases hc
      exact translated_k a b
  | s a b d =>
      cases hc
      exact translated_s a b d
  | classical a =>
      cases hc
      exact translated_classical a
  | allElim a x t =>
      cases hc
      exact h.allElim a x t
  | allImp a b x =>
      cases hc
      exact h.allImp a b x
  | vacuous a x =>
      by_cases hx : x ∉ a.freeVarFinset
      · simp only [Certificates.logicalDecode, if_pos hx, Option.some.injEq] at hc
        subst φ
        exact h.vacuous a x hx
      · simp [Certificates.logicalDecode, hx] at hc
  | eqRefl t =>
      cases hc
      exact h.eqRefl t
  | eqSubst a x t u =>
      cases hc
      exact h.eqSubst a x t u

/-- Assemble the guarded compiler interface without hiding its remaining
axiom and rule obligations. -/
def guardedHandlers (h : RemainingLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ))
    (modusPonens : ∀ φ ψ, KDerivation (guardedCode (φ.imp ψ)) →
      KDerivation (guardedCode φ) → KDerivation (guardedCode ψ))
    (generalization : ∀ x φ, KDerivation (guardedCode φ) →
      KDerivation (guardedCode (FOL.allAt x φ))) : PAtoCompactGuardedBridge.Handlers where
  logical := logicalHandler h
  arithmetic := arithmetic
  modusPonens := modusPonens
  generalization := generalization

end PASoundness.PAtoCompactGuardedPropositional

#print axioms PASoundness.PAtoCompactGuardedPropositional.guardedOfUnconditional
#print axioms PASoundness.PAtoCompactGuardedPropositional.translated_k
#print axioms PASoundness.PAtoCompactGuardedPropositional.translated_s
#print axioms PASoundness.PAtoCompactGuardedPropositional.translated_classical
#print axioms PASoundness.PAtoCompactGuardedPropositional.logicalHandler
#print axioms PASoundness.PAtoCompactGuardedPropositional.guardedHandlers
