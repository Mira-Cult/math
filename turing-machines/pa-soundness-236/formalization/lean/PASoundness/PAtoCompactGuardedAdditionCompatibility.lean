import PASoundness.PAtoCompactGuardedAdditionTwoLogical
import PASoundness.PAtoCompactGuardedCompatibilityBridge

/-! Compose the checked arithmetic handlers with the occurrence-conditioned
universal-elimination reduction. The displayed compatibility and equality-
substitution proofs, and both multiplication axiom families, remain explicit
finite K proof-data inputs. This is not an executable proof extractor. -/

namespace PASoundness.PAtoCompactGuardedAdditionCompatibility

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- Assemble the guarded compiler under the explicit occurrence-conditioned
substitution-compatibility, equality-substitution, and multiplication inputs. -/
noncomputable def handlers
    (logical : PAtoCompactGuardedCompatibilityBridge.CompatibilityInputs)
    (arithmetic : PAtoCompactGuardedAdditionBridge.RemainingArithmetic) :
    PAtoCompactGuardedBridge.Handlers :=
  PAtoCompactGuardedAdditionTwoLogical.handlers
    (PAtoCompactGuardedCompatibilityBridge.twoLogical logical) arithmetic

/-- Translate an actual checked PA proof certificate under the displayed
compatibility, equality-substitution, and multiplication proof inputs. -/
noncomputable def translateChecked
    (logical : PAtoCompactGuardedCompatibilityBridge.CompatibilityInputs)
    (arithmetic : PAtoCompactGuardedAdditionBridge.RemainingArithmetic)
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) : KDerivation (guardedCode φ) :=
  PAtoCompactGuardedBridge.translateChecked (handlers logical arithmetic) c φ hc

theorem translated_certificate
    (logical : PAtoCompactGuardedCompatibilityBridge.CompatibilityInputs)
    (arithmetic : PAtoCompactGuardedAdditionBridge.RemainingArithmetic)
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked logical arithmetic c φ hc)) = guardedCode φ :=
  certificate_correct _

/-- Literal machine acceptance is equivalent to PA soundness under the
displayed compatibility, equality-substitution, and multiplication inputs. -/
theorem selected_accepts_iff_pa_soundness
    (logical : PAtoCompactGuardedCompatibilityBridge.CompatibilityInputs)
    (arithmetic : PAtoCompactGuardedAdditionBridge.RemainingArithmetic) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PAtoCompactGuardedBridge.selected_accepts_iff_pa_soundness (handlers logical arithmetic)

end PASoundness.PAtoCompactGuardedAdditionCompatibility

#print axioms PASoundness.PAtoCompactGuardedAdditionCompatibility.handlers
#print axioms PASoundness.PAtoCompactGuardedAdditionCompatibility.translateChecked
#print axioms PASoundness.PAtoCompactGuardedAdditionCompatibility.translated_certificate
#print axioms PASoundness.PAtoCompactGuardedAdditionCompatibility.selected_accepts_iff_pa_soundness
