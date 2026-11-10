import PASoundness.PAtoCompactFirstFactorCutFrameAdapter
import PASoundness.PAtoCompactReversedArithmeticLeaves
import PASoundness.PAtoCompactMulReversalGraphBridge

/-! Compose the first-factor successor construction with the checked-proof
multiplication-reversal compiler. All imported task drafts require kernel
validation. The two uniform graph-law families remain explicit inputs. -/

namespace PASoundness.PAtoCompactFirstFactorReversalBridge

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactEqSubstFromUniformGraphLaws
open PASoundness.PAtoCompactMulReversalCompilerAdapter
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- The same first-factor equation expected by the reversed arithmetic leaf
compiler. This is a source-level assembly of the imported construction. -/
noncomputable def firstFactor : PASoundness.PAtoCompactReversedArithmeticLeaves.FirstFactorSuccessor :=
  PASoundness.PAtoCompactFirstFactorCutFrameAdapter.guarded_first_factor_successor

/-- The reversed arithmetic leaves, including the original PA second-factor
multiplication-successor axiom, are obtained from the first-factor family. -/
noncomputable def arithmetic : ReversedArithmeticLeaves :=
  PASoundness.PAtoCompactReversedArithmeticLeaves.arithmetic firstFactor

/-- Translate a checked PA proof assuming the two explicit uniform guarded
term-graph laws. This is finite proof data, not an executable extractor from
arbitrary PA derivability. -/
noncomputable def translateChecked (output : UniformOutput) (functional : UniformFunctionality)
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) : KDerivation (guardedCode φ) :=
  PASoundness.PAtoCompactMulReversalGraphBridge.translateChecked output functional arithmetic c φ hc

theorem translated_certificate (output : UniformOutput) (functional : UniformFunctionality)
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked output functional c φ hc)) = guardedCode φ :=
  certificate_correct _

/-- Literal machine acceptance is equivalent to PA soundness under the two
explicit guarded graph-law families. These assumptions remain unproved here. -/
theorem selected_accepts_iff_pa_soundness (output : UniformOutput)
    (functional : UniformFunctionality) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PASoundness.PAtoCompactMulReversalGraphBridge.selected_accepts_iff_pa_soundness
    output functional arithmetic

end PASoundness.PAtoCompactFirstFactorReversalBridge

#print axioms PASoundness.PAtoCompactFirstFactorReversalBridge.firstFactor
#print axioms PASoundness.PAtoCompactFirstFactorReversalBridge.arithmetic
#print axioms PASoundness.PAtoCompactFirstFactorReversalBridge.translateChecked
#print axioms PASoundness.PAtoCompactFirstFactorReversalBridge.translated_certificate
#print axioms PASoundness.PAtoCompactFirstFactorReversalBridge.selected_accepts_iff_pa_soundness
