import PASoundness.PAtoCompactUniformOutputFromBinaryRoots
import PASoundness.PAtoCompactProductOutputGuardedHandler
import PASoundness.PAtoCompactUniformFunctionalityAdditionAdapter
import PASoundness.PAtoCompactFirstFactorReversalBridge

/-! Compose the PA-to-compact proof translation while retaining only the
addition-root guarded output-transport family as explicit input. Several
imported task sources are not yet independently Lean-validated. This module
does not construct the remaining family. -/

namespace PASoundness.PAtoCompactBridgeFromAdditionOutput

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstBinaryStep
open PASoundness.PAtoCompactGuardedOutputReplacement
open PASoundness.PAtoCompactEqSubstFromUniformGraphLaws
open PASoundness.PAtoCompactUniformOutputFromBinaryRoots
open PASoundness.PAtoCompactGuardedBridge
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- The remaining guarded output proof family at addition roots, for every
guard and arbitrary PA operand terms. It is an explicit finite-K input. -/
abbrev AdditionOutput : Type := ∀ (g : PASoundness.CompactNamed.Formula) (t u : Peano.Term),
  GuardedOutputTransport g (Peano.add t u)

/-- Supply the product-root family from the product-output construction and
retain the addition-root family as an input. -/
noncomputable def output (addition : AdditionOutput) : UniformOutput := by
  apply uniform_output
  refine ⟨addition, ?_⟩
  intro g t u
  simpa [Peano.mul, PASoundness.PAtoCompactTermZeroGuarded.binaryTerm] using
    PASoundness.PAtoCompactProductOutputGuardedHandler.guarded_product_output g t u

/-- Translate a checked PA proof using the displayed addition-root family.
All proof data comes from the composed object-level constructors. -/
noncomputable def translateChecked (addition : AdditionOutput)
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) : KDerivation (guardedCode φ) :=
  PASoundness.PAtoCompactFirstFactorReversalBridge.translateChecked (output addition)
    PASoundness.PAtoCompactUniformFunctionalityAdditionAdapter.uniform_functionality c φ hc

theorem translated_certificate (addition : AdditionOutput)
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked addition c φ hc)) = guardedCode φ :=
  certificate_correct _

/-- Literal-machine guarded acceptance is equivalent to PA soundness,
conditional on the displayed addition-root output proof family. -/
theorem selected_accepts_iff_pa_soundness (addition : AdditionOutput) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PASoundness.PAtoCompactFirstFactorReversalBridge.selected_accepts_iff_pa_soundness
    (output addition) PASoundness.PAtoCompactUniformFunctionalityAdditionAdapter.uniform_functionality

end PASoundness.PAtoCompactBridgeFromAdditionOutput

#print axioms PASoundness.PAtoCompactBridgeFromAdditionOutput.AdditionOutput
#print axioms PASoundness.PAtoCompactBridgeFromAdditionOutput.output
#print axioms PASoundness.PAtoCompactBridgeFromAdditionOutput.translateChecked
#print axioms PASoundness.PAtoCompactBridgeFromAdditionOutput.translated_certificate
#print axioms PASoundness.PAtoCompactBridgeFromAdditionOutput.selected_accepts_iff_pa_soundness
