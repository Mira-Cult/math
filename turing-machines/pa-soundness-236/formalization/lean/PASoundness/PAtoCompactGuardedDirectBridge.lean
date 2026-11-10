import PASoundness.PAtoCompactGuardedThreeLogical
import PASoundness.PAtoCompactDirectGeneralization

/-! Assemble the guarded PA-to-K compiler using the proved generalization
transformer. The three remaining logical axiom families and every PA axiom,
including induction, are explicit finite K proof-data inputs. This assembly is
noncomputable and is not an executable proof extractor. -/
namespace PASoundness.PAtoCompactGuardedDirectBridge

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- Build the guarded compiler interface using the proved modus-ponens and
generalization transformations, with the remaining axiom proofs supplied. -/
noncomputable def handlers (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ)) :
    PAtoCompactGuardedBridge.Handlers :=
  PAtoCompactGuardedModusPonensFull.handlers
    (PAtoCompactGuardedFourLogical.remainingLogical
      (PAtoCompactGuardedThreeLogical.fourLogical logical))
    arithmetic PAtoCompactDirectGeneralization.generalization_unconditional

/-- Translate an actual checked PA proof certificate to finite K proof data
under the three logical and full PA-axiom handlers. -/
noncomputable def translateChecked (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ))
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) : KDerivation (guardedCode φ) :=
  PAtoCompactGuardedBridge.translateChecked (handlers logical arithmetic) c φ hc

theorem translated_certificate (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ))
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked logical arithmetic c φ hc)) = guardedCode φ :=
  certificate_correct _

/-- Literal machine acceptance is equivalent to PA soundness conditional on
the displayed three logical-family handlers and the full PA-axiom handler. -/
theorem selected_accepts_iff_pa_soundness
    (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ)) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PAtoCompactGuardedBridge.selected_accepts_iff_pa_soundness (handlers logical arithmetic)

end PASoundness.PAtoCompactGuardedDirectBridge

#print axioms PASoundness.PAtoCompactGuardedDirectBridge.handlers
#print axioms PASoundness.PAtoCompactGuardedDirectBridge.translateChecked
#print axioms PASoundness.PAtoCompactGuardedDirectBridge.translated_certificate
#print axioms PASoundness.PAtoCompactGuardedDirectBridge.selected_accepts_iff_pa_soundness
