import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactPropositionalHandlers

/-! Discharge the translated vacuous logical leaf using the compiler's
existing generalization bridge. Four logical families, the PA axiom handler,
and generalization remain explicit inputs. The unguarded `FourLogical`
interface is uninhabitable; see `PAtoCompactOpenAxiomCounterexample`. -/
namespace PASoundness.PAtoCompactVacuousHandler

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactPropositionalHandlers
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- The logical proof-data obligations remaining after the propositional and
vacuous families have been constructed. -/
structure FourLogical where
  allElim : ∀ (φ : Peano.Formula) (x : Nat) (t : Peano.Term),
    KDerivation (code ((FOL.allAt x φ).imp (FOL.substAt φ x t)))
  allImp : ∀ (φ ψ : Peano.Formula) (x : Nat),
    KDerivation (code ((FOL.allAt x (φ.imp ψ)).imp
      ((FOL.allAt x φ).imp (FOL.allAt x ψ))))
  eqRefl : ∀ (t : Peano.Term), KDerivation (code (t.equal t))
  eqSubst : ∀ (φ : Peano.Formula) (x : Nat) (t u : Peano.Term),
    KDerivation (code ((t.equal u).imp ((FOL.substAt φ x t).imp (FOL.substAt φ x u))))

/-- Reuse the generalization bridge to supply the vacuous logical family. -/
def remainingLogical (h : FourLogical)
    (generalization : ∀ x φ, KDerivation (imp (allCode x (code φ)) (code (FOL.allAt x φ)))) :
    RemainingLogical where
  allElim := h.allElim
  allImp := h.allImp
  vacuous := fun φ x hx => translated_vacuous_leaf φ x hx (generalization x φ)
  eqRefl := h.eqRefl
  eqSubst := h.eqSubst

/-- Concrete handlers with the vacuous family constructed rather than
supplied separately. The displayed four families and PA/generalization
handlers remain proof-data inputs. -/
def concreteHandlers (h : FourLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (code φ))
    (generalization : ∀ x φ, KDerivation (imp (allCode x (code φ)) (code (FOL.allAt x φ)))) :
    PAtoCompactConcreteBridge.Handlers :=
  PAtoCompactPropositionalHandlers.concreteHandlers (remainingLogical h generalization)
    arithmetic generalization

/-- The literal machine/PA soundness equivalence under the narrowed
proof-data obligations above. -/
theorem selected_accepts_iff_pa_soundness (h : FourLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (code φ))
    (generalization : ∀ x φ, KDerivation (imp (allCode x (code φ)) (code (FOL.allAt x φ)))) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PAtoCompactConcreteBridge.selected_accepts_iff_pa_soundness
    (concreteHandlers h arithmetic generalization)

end PASoundness.PAtoCompactVacuousHandler

#print axioms PASoundness.PAtoCompactVacuousHandler.remainingLogical
#print axioms PASoundness.PAtoCompactVacuousHandler.concreteHandlers
#print axioms PASoundness.PAtoCompactVacuousHandler.selected_accepts_iff_pa_soundness
