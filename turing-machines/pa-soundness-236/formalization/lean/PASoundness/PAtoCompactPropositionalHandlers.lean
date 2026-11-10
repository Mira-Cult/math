import PASoundness.PAtoCompactConcreteBridge
import PASoundness.CompactDerivations

/-! Actual K proof data for the propositional logical axiom leaves of the
concrete PA translation. Quantifier, equality, arithmetic and generalization
handlers remain separate obligations. -/
namespace PASoundness.PAtoCompactPropositionalHandlers

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactHilbertBasis PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation

/-- Concrete translation preserves the source negation encoding. -/
theorem code_not (φ : Peano.Formula) : code φ.not = neg (code φ) := rfl

/-- The translated K axiom is a finite K derivation. -/
def translated_k (φ ψ : Peano.Formula) :
    KDerivation (code (φ.imp (ψ.imp φ))) := by
  rw [code_imp, code_imp]
  exact weakening (code φ) (code ψ)

/-- The translated S axiom is a finite K derivation. -/
def translated_s (φ ψ χ : Peano.Formula) :
    KDerivation (code ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))) := by
  simp only [code_imp]
  exact distribution (code φ) (code ψ) (code χ)

/-- The translated classical double-negation axiom is a finite K derivation. -/
def translated_classical (φ : Peano.Formula) : KDerivation (code (φ.not.not.imp φ)) := by
  rw [code_imp, code_not, code_not]
  exact doubleNegElim (code φ)

theorem translated_k_certificate (φ ψ : Peano.Formula) :
    theoremCode (certificate (translated_k φ ψ)) = code (φ.imp (ψ.imp φ)) :=
  certificate_correct _

theorem translated_s_certificate (φ ψ χ : Peano.Formula) :
    theoremCode (certificate (translated_s φ ψ χ)) =
      code ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ))) :=
  certificate_correct _

theorem translated_classical_certificate (φ : Peano.Formula) :
    theoremCode (certificate (translated_classical φ)) = code (φ.not.not.imp φ) :=
  certificate_correct _

/-- The five nonpropositional logical leaf families still needing explicit K
proof data. These are syntactic obligations, not truth assumptions. -/
structure RemainingLogical where
  allElim : ∀ (φ : Peano.Formula) (x : Nat) (t : Peano.Term),
    KDerivation (code ((FOL.allAt x φ).imp (FOL.substAt φ x t)))
  allImp : ∀ (φ ψ : Peano.Formula) (x : Nat),
    KDerivation (code ((FOL.allAt x (φ.imp ψ)).imp
      ((FOL.allAt x φ).imp (FOL.allAt x ψ))))
  vacuous : ∀ (φ : Peano.Formula) (x : Nat), x ∉ φ.freeVarFinset →
    KDerivation (code (φ.imp (FOL.allAt x φ)))
  eqRefl : ∀ (t : Peano.Term), KDerivation (code (t.equal t))
  eqSubst : ∀ (φ : Peano.Formula) (x : Nat) (t u : Peano.Term),
    KDerivation (code ((t.equal u).imp ((FOL.substAt φ x t).imp (FOL.substAt φ x u))))

/-- Assemble the exact logical-leaf handler from the three constructed
propositional families and the five explicitly supplied remaining families. -/
def logicalHandler (h : RemainingLogical) (c : Certificates.LogicalCode Peano.language)
    (φ : Peano.Formula) (hc : Certificates.logicalDecode c = some φ) : KDerivation (code φ) := by
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

/-- The conditional concrete bridge now needs only the five displayed
nonpropositional logical families, PA axiom handlers, and generalization. -/
def concreteHandlers (h : RemainingLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (code φ))
    (generalization : ∀ x φ, KDerivation (imp (allCode x (code φ)) (code (FOL.allAt x φ)))) :
    PAtoCompactConcreteBridge.Handlers where
  logical := logicalHandler h
  arithmetic := arithmetic
  generalization := generalization

end PASoundness.PAtoCompactPropositionalHandlers

#print axioms PASoundness.PAtoCompactPropositionalHandlers.translated_k
#print axioms PASoundness.PAtoCompactPropositionalHandlers.translated_s
#print axioms PASoundness.PAtoCompactPropositionalHandlers.translated_classical
