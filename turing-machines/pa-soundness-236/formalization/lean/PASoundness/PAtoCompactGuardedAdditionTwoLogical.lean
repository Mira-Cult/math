import PASoundness.PAtoCompactGuardedAdditionBridge
import PASoundness.PAtoCompactGuardedTwoLogical

/-! Compose guarded equality reflexivity with the constructed induction,
successor and addition axiom handlers. Universal elimination, equality
substitution, and the two multiplication axiom families remain explicit finite
K proof-data inputs. This is not an executable proof extractor. -/

namespace PASoundness.PAtoCompactGuardedAdditionTwoLogical

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- Assemble the guarded compiler with the proved induction, successor,
addition, and equality-reflexivity handlers. -/
noncomputable def handlers (logical : PAtoCompactGuardedTwoLogical.TwoLogical)
    (arithmetic : PAtoCompactGuardedAdditionBridge.RemainingArithmetic) :
    PAtoCompactGuardedBridge.Handlers :=
  PAtoCompactGuardedAdditionBridge.handlers
    (PAtoCompactGuardedTwoLogical.threeLogical logical) arithmetic

/-- Translate a checked PA proof certificate to finite K proof data under
the two remaining logical and two multiplication handler families. -/
noncomputable def translateChecked (logical : PAtoCompactGuardedTwoLogical.TwoLogical)
    (arithmetic : PAtoCompactGuardedAdditionBridge.RemainingArithmetic)
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) : KDerivation (guardedCode φ) :=
  PAtoCompactGuardedBridge.translateChecked (handlers logical arithmetic) c φ hc

theorem translated_certificate (logical : PAtoCompactGuardedTwoLogical.TwoLogical)
    (arithmetic : PAtoCompactGuardedAdditionBridge.RemainingArithmetic)
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked logical arithmetic c φ hc)) = guardedCode φ :=
  certificate_correct _

/-- Literal machine acceptance is equivalent to PA soundness under the
displayed two logical and two multiplication handler families. -/
theorem selected_accepts_iff_pa_soundness
    (logical : PAtoCompactGuardedTwoLogical.TwoLogical)
    (arithmetic : PAtoCompactGuardedAdditionBridge.RemainingArithmetic) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PAtoCompactGuardedBridge.selected_accepts_iff_pa_soundness (handlers logical arithmetic)

end PASoundness.PAtoCompactGuardedAdditionTwoLogical

#print axioms PASoundness.PAtoCompactGuardedAdditionTwoLogical.handlers
#print axioms PASoundness.PAtoCompactGuardedAdditionTwoLogical.translateChecked
#print axioms PASoundness.PAtoCompactGuardedAdditionTwoLogical.translated_certificate
#print axioms PASoundness.PAtoCompactGuardedAdditionTwoLogical.selected_accepts_iff_pa_soundness
