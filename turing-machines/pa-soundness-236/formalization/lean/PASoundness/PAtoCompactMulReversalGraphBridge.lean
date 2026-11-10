import PASoundness.PAtoCompactMulReversalCompilerAdapter
import PASoundness.PAtoCompactGuardedGraphLawsBridge

/-! Connect the multiplication-reversal compiler to the existing guarded
PA-to-K bridge. Uniform output transport, uniform functionality, and all
reversed arithmetic leaf proofs remain explicit inputs. The final equivalence
here is conditional on those inputs; this module does not construct them. -/

namespace PASoundness.PAtoCompactMulReversalGraphBridge

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactEqSubstFromUniformGraphLaws
open PASoundness.PAtoCompactMulReversalCompilerAdapter
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- The two explicit graph-law families supply the guarded logical families
needed by the multiplication-reversal compiler. -/
noncomputable def logical (output : UniformOutput) (functional : UniformFunctionality) :
    PAtoCompactGuardedThreeLogical.ThreeLogical :=
  PAtoCompactGuardedTwoLogical.threeLogical
    (PAtoCompactAllElimFromUniformGuardedGraphLaws.twoLogical output functional)

/-- Assemble the PA-to-K handlers given the two graph-law families and the
still-explicit finite K proofs of all reversed PA arithmetic leaves. -/
noncomputable def handlers (output : UniformOutput) (functional : UniformFunctionality)
    (arithmetic : ReversedArithmeticLeaves) : PAtoCompactGuardedBridge.Handlers :=
  PAtoCompactGuardedGraphLawsBridge.handlers output functional
    (mulSucc (logical output functional) arithmetic)

/-- Translate an actual checked PA proof under the displayed proof-family
assumptions. The translated certificate is obtained from finite proof data;
no executable extraction from PA derivability is claimed. -/
noncomputable def translateChecked (output : UniformOutput) (functional : UniformFunctionality)
    (arithmetic : ReversedArithmeticLeaves) (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) : KDerivation (guardedCode φ) :=
  PAtoCompactGuardedBridge.translateChecked (handlers output functional arithmetic) c φ hc

theorem translated_certificate (output : UniformOutput) (functional : UniformFunctionality)
    (arithmetic : ReversedArithmeticLeaves) (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked output functional arithmetic c φ hc)) =
      guardedCode φ := certificate_correct _

/-- The literal-machine acceptance/PA-soundness equivalence follows under the
three explicitly supplied finite-K proof families; the premises are not
constructed by this result. -/
theorem selected_accepts_iff_pa_soundness
    (output : UniformOutput) (functional : UniformFunctionality)
    (arithmetic : ReversedArithmeticLeaves) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PAtoCompactGuardedBridge.selected_accepts_iff_pa_soundness
    (handlers output functional arithmetic)

end PASoundness.PAtoCompactMulReversalGraphBridge

#print axioms PASoundness.PAtoCompactMulReversalGraphBridge.logical
#print axioms PASoundness.PAtoCompactMulReversalGraphBridge.handlers
#print axioms PASoundness.PAtoCompactMulReversalGraphBridge.translateChecked
#print axioms PASoundness.PAtoCompactMulReversalGraphBridge.translated_certificate
#print axioms PASoundness.PAtoCompactMulReversalGraphBridge.selected_accepts_iff_pa_soundness
