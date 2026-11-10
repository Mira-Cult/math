import PASoundness.PAtoCompactScopedUnusedFull
import PASoundness.PAtoCompactGeneralizationConditional

/-! Discharge the vacuous logical axiom in the guarded PA-to-K compiler.
The four other nonpropositional logical families, every PA axiom (including
induction), and guarded-body alignment remain explicit finite-K-proof inputs.
The proof-data assembly is noncomputable and is not an executable extractor. -/
namespace PASoundness.PAtoCompactGuardedFourLogical

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- The four logical axiom families not yet supplied by the guarded compiler. -/
structure FourLogical where
  allElim : ∀ (φ : Peano.Formula) (x : Nat) (t : Peano.Term),
    KDerivation (guardedCode ((FOL.allAt x φ).imp (FOL.substAt φ x t)))
  allImp : ∀ (φ ψ : Peano.Formula) (x : Nat),
    KDerivation (guardedCode ((FOL.allAt x (φ.imp ψ)).imp
      ((FOL.allAt x φ).imp (FOL.allAt x ψ))))
  eqRefl : ∀ (t : Peano.Term), KDerivation (guardedCode (t.equal t))
  eqSubst : ∀ (φ : Peano.Formula) (x : Nat) (t u : Peano.Term),
    KDerivation (guardedCode ((t.equal u).imp ((FOL.substAt φ x t).imp (FOL.substAt φ x u))))

/-- Assemble all five nonpropositional logical families using the proved
vacuity family and the four displayed proof-data inputs. -/
noncomputable def remainingLogical (h : FourLogical) :
    PAtoCompactGuardedPropositional.RemainingLogical where
  allElim := h.allElim
  allImp := h.allImp
  vacuous := PAtoCompactScopedUnusedFull.vacuous_all
  eqRefl := h.eqRefl
  eqSubst := h.eqSubst

/-- Assemble the checked-proof compiler's handler structure. Generalization
still depends on guarded body alignment, and arithmetic includes induction. -/
noncomputable def handlers (alignment : PAtoCompactGeneralizationConditional.BodyAlignment)
    (logical : FourLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ)) :
    PAtoCompactGuardedBridge.Handlers :=
  PAtoCompactGeneralizationConditional.handlers alignment (remainingLogical logical) arithmetic

/-- The literal machine/PA equivalence remains conditional on the displayed
body alignment, four logical families and the full PA axiom handler. -/
theorem selected_accepts_iff_pa_soundness
    (alignment : PAtoCompactGeneralizationConditional.BodyAlignment)
    (logical : FourLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ)) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PAtoCompactGuardedBridge.selected_accepts_iff_pa_soundness
    (handlers alignment logical arithmetic)

end PASoundness.PAtoCompactGuardedFourLogical

#print axioms PASoundness.PAtoCompactGuardedFourLogical.remainingLogical
#print axioms PASoundness.PAtoCompactGuardedFourLogical.handlers
#print axioms PASoundness.PAtoCompactGuardedFourLogical.selected_accepts_iff_pa_soundness
