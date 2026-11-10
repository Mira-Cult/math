import PASoundness.PAtoCompactBridgeFromAdditionOutput
import PASoundness.PAtoCompactAdditionOutputGraphHandler
import PASoundness.PeanoCompactProofToPAClosed
import PASoundness.M236ObserverFrontDoor

/-! End-to-end specialization of the checked PA/compact proof translations and
literal M236 observer. Independent source-review and Lean verification evidence
for the exact reviewed revision is recorded in M236-CONTINUATION.md.
The finite proof-data construction uses classical choice and does not claim
an executable extractor from arbitrary PA derivability. -/
namespace PASoundness.PAtoCompactEndToEndProofTranslation

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactGuardedBridge
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- Addition-root guarded output transport, specialized to the ordinary PA
addition term constructor. No caller-supplied operation or child proof is an
input. The underlying finite K proof construction is noncomputable. -/
noncomputable def additionOutput :
    PASoundness.PAtoCompactBridgeFromAdditionOutput.AdditionOutput := by
  intro g t u
  simpa [Peano.add, PASoundness.PAtoCompactTermZeroGuarded.binaryTerm] using
    PASoundness.PAtoCompactAdditionOutputGraphHandler.guarded_addition_root_output g t u

/-- Transform each supplied checked PA proof certificate into finite K proof
data for the guarded translation of its checked conclusion. -/
noncomputable def translateChecked (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) : KDerivation (guardedCode φ) :=
  PASoundness.PAtoCompactBridgeFromAdditionOutput.translateChecked additionOutput c φ hc

/-- The generated K certificate checks to exactly the guarded translation. -/
theorem translated_certificate (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked c φ hc)) = guardedCode φ :=
  certificate_correct _

/-- The guarded PA-to-K formula translation preserves and reflects standard
truth on every ordinal-coded assignment. -/
theorem guarded_translation_truth (φ : Peano.Formula) (v : Nat → Nat) :
    (CompactMatrix.decode (guardedCode φ)).Realize
      (PAtoCompactOpenScope.ordinalAssignment v) ↔ φ.Realize v :=
  PASoundness.PAtoCompactGuardedBridge.guarded_truth φ v

/-- The other proof direction translates any finite compact derivation to
an explicit PA derivation of its open arithmetic interpretation. -/
theorem compact_derivation_to_pa {f : Nat} (d : KDerivation f) :
    Peano.FormulaProves (CompactLogicalTransport.interpreted f) :=
  PeanoCompactProofToPAClosed.derivation_to_pa d

/-- The compact-to-PA formula interpretation preserves and reflects standard
truth separately from its proof translation. -/
theorem compact_translation_truth (f : Nat) (ρ : Nat → Nat) :
    (CompactLogicalTransport.interpreted f).Realize ρ ↔
      (CompactMatrix.decode f).Realize ρ :=
  PeanoCompactProofToPAClosed.translation_truth f ρ

/-- Literal blank-start M236 passes its guarded omega observer exactly when
every PA-provable sentence is true in the standard natural numbers. The two
proof-translation and truth-preservation directions are exposed above. -/
theorem selected_accepts_iff_pa_soundness :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PASoundness.PAtoCompactBridgeFromAdditionOutput.selected_accepts_iff_pa_soundness additionOutput

/-- Explicit observer front door: a well-formed complete trace, frame
progress, and a separate winning strategy for each positive-rank game are
equivalent to standard PA soundness. -/
theorem selected_guards_and_strategies_iff_pa_soundness :
    ((Complete (wordDecodedEvents (machineWordSystem M236.machine M236.machineLabels)) ∧
        FrameProgress (machineWordSystem M236.machine M236.machineLabels)) ∧
      ∀ n, 0 < n → ∀ p, ∃ s : Strategy .ex n,
        Winning s (fun xs => Emitted
          (wordDecodedEvents (machineWordSystem M236.machine M236.machineLabels))
          false ⟨n, p, xs⟩)) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) :=
  PASoundness.M236ObserverFrontDoor.selected_trace_iff_complete_and_strategies.symm.trans
    selected_accepts_iff_pa_soundness

end PASoundness.PAtoCompactEndToEndProofTranslation

#print axioms PASoundness.PAtoCompactEndToEndProofTranslation.additionOutput
#print axioms PASoundness.PAtoCompactEndToEndProofTranslation.translateChecked
#print axioms PASoundness.PAtoCompactEndToEndProofTranslation.translated_certificate
#print axioms PASoundness.PAtoCompactEndToEndProofTranslation.guarded_translation_truth
#print axioms PASoundness.PAtoCompactEndToEndProofTranslation.compact_derivation_to_pa
#print axioms PASoundness.PAtoCompactEndToEndProofTranslation.compact_translation_truth
#print axioms PASoundness.PAtoCompactEndToEndProofTranslation.selected_accepts_iff_pa_soundness
#print axioms PASoundness.PAtoCompactEndToEndProofTranslation.selected_guards_and_strategies_iff_pa_soundness
