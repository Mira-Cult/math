import PASoundness.PAtoCompactAllElimFromUniformGuardedGraphLaws
import PASoundness.PAtoCompactGuardedMulZeroCompatibility

/-! Compose the guarded PA-to-K compiler using the two displayed uniform
term-graph proof families. Guarded output transport, guarded graph
functionality, and the multiplication-successor axiom family remain explicit
finite K proof-data inputs. This is not an executable proof extractor. -/

namespace PASoundness.PAtoCompactGuardedGraphLawsBridge

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactEqSubstFromUniformGraphLaws
open PASoundness.PAtoCompactGuardedMulZeroCompatibility
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- Assemble the guarded compiler conditional on uniform guarded term-graph
output transport and functionality, and on multiplication successor. -/
noncomputable def handlers (output : UniformOutput) (functional : UniformFunctionality)
    (mulSucc : MulSuccHandler) : PAtoCompactGuardedBridge.Handlers :=
  PAtoCompactGuardedAdditionTwoLogical.handlers
    (PAtoCompactAllElimFromUniformGuardedGraphLaws.twoLogical output functional)
    (withMulZero mulSucc)

/-- Translate a checked PA certificate to finite K proof data under the
three displayed proof-family inputs. -/
noncomputable def translateChecked (output : UniformOutput) (functional : UniformFunctionality)
    (mulSucc : MulSuccHandler) (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) : KDerivation (guardedCode φ) :=
  PAtoCompactGuardedBridge.translateChecked (handlers output functional mulSucc) c φ hc

theorem translated_certificate (output : UniformOutput) (functional : UniformFunctionality)
    (mulSucc : MulSuccHandler) (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked output functional mulSucc c φ hc)) =
      guardedCode φ := certificate_correct _

/-- Literal machine acceptance is equivalent to PA soundness conditional on
the displayed two guarded graph-law families and multiplication successor. -/
theorem selected_accepts_iff_pa_soundness
    (output : UniformOutput) (functional : UniformFunctionality) (mulSucc : MulSuccHandler) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PAtoCompactGuardedBridge.selected_accepts_iff_pa_soundness (handlers output functional mulSucc)

end PASoundness.PAtoCompactGuardedGraphLawsBridge

#print axioms PASoundness.PAtoCompactGuardedGraphLawsBridge.handlers
#print axioms PASoundness.PAtoCompactGuardedGraphLawsBridge.translateChecked
#print axioms PASoundness.PAtoCompactGuardedGraphLawsBridge.translated_certificate
#print axioms PASoundness.PAtoCompactGuardedGraphLawsBridge.selected_accepts_iff_pa_soundness
