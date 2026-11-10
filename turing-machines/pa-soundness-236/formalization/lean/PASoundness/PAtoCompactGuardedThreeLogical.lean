import PASoundness.PAtoCompactGuardedFourLogical
import PASoundness.PAtoCompactGuardedAllImp

/-! Supply the proved vacuity and universal-distribution families to the
guarded PA-to-K compiler. The three other nonpropositional logical families,
every PA axiom (including induction), and guarded-body alignment remain
explicit finite-K-proof inputs. This noncomputable assembly is not an
executable proof extractor. -/
namespace PASoundness.PAtoCompactGuardedThreeLogical

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- The three logical axiom families not yet supplied by the compiler. -/
structure ThreeLogical where
  allElim : ∀ (φ : Peano.Formula) (x : Nat) (t : Peano.Term),
    KDerivation (guardedCode ((FOL.allAt x φ).imp (FOL.substAt φ x t)))
  eqRefl : ∀ (t : Peano.Term), KDerivation (guardedCode (t.equal t))
  eqSubst : ∀ (φ : Peano.Formula) (x : Nat) (t u : Peano.Term),
    KDerivation (guardedCode ((t.equal u).imp ((FOL.substAt φ x t).imp (FOL.substAt φ x u))))

/-- Fill the universal-distribution field with its proved K derivation. -/
noncomputable def fourLogical (h : ThreeLogical) :
    PAtoCompactGuardedFourLogical.FourLogical where
  allElim := h.allElim
  allImp := PAtoCompactGuardedAllImp.allImp
  eqRefl := h.eqRefl
  eqSubst := h.eqSubst

/-- Assemble the proof compiler's handlers with vacuity and universal
distribution discharged; arithmetic includes the full induction schema. -/
noncomputable def handlers (alignment : PAtoCompactGeneralizationConditional.BodyAlignment)
    (logical : ThreeLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ)) :
    PAtoCompactGuardedBridge.Handlers :=
  PAtoCompactGuardedFourLogical.handlers alignment (fourLogical logical) arithmetic

/-- Literal machine acceptance is equivalent to PA soundness under the
displayed body-alignment, three logical-family and PA-axiom proof inputs. -/
theorem selected_accepts_iff_pa_soundness
    (alignment : PAtoCompactGeneralizationConditional.BodyAlignment)
    (logical : ThreeLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ)) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PAtoCompactGuardedBridge.selected_accepts_iff_pa_soundness
    (handlers alignment logical arithmetic)

end PASoundness.PAtoCompactGuardedThreeLogical

#print axioms PASoundness.PAtoCompactGuardedThreeLogical.fourLogical
#print axioms PASoundness.PAtoCompactGuardedThreeLogical.handlers
#print axioms PASoundness.PAtoCompactGuardedThreeLogical.selected_accepts_iff_pa_soundness
