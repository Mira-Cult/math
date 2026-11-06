import Shared.Beeping.NPcoNP.Source284OriginalCutoffVerifier
import Shared.ComplexityBridge.TM2ProtectedVerifierComposition

/-! A finite verifier for the encoded joined input, retaining the original
witness cutoff. This is a bounded verifier result; its source and physical
table connections are separate obligations. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284JoinedFiniteVerifier

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284JoinedFrames
open Shared.Codes.FinitePrograms

theorem guarded_bounded (p : Polynomial Nat) (R : List Bool × List Bool → Bool)
    (hR : IsPolyTime R) :
    ∃ (verifier : Program) (clock : Polynomial Nat), valid verifier = true ∧
      ∀ x w : List Bool,
        let packed := BitstringEncoding.bitEncode (joinedBits x w, ([] : List Bool))
        bounded verifier packed (clock.eval packed.length) =
          some (if w.length ≤ p.eval x.length then R (x,w) else false) := by
  let guarded := Source284OriginalCutoffVerifier.guarded p R
  obtain ⟨raw,clock,hcorrect⟩ := FiniteVerifierCompiler.canonical_finite_verifier_compiler
    (Source284JoinedDecodeTM2.pairedRelation guarded)
    (Source284JoinedDecodeTM2.pairedRelation_isPolyTime guarded
      (Source284OriginalCutoffVerifier.guarded_isPolyTime p R hR))
  let verifier := Shared.Codes.FiniteProgramRepair.repair raw
  refine ⟨verifier,clock,Shared.Codes.FiniteProgramRepair.repair_valid raw,?_⟩
  intro x w
  have hd : Source284JoinedDecodeTM2.decode (joinedBits x w) = (x,w) := by
    simpa using Source284JoinedDecodeTM2.decode_correct x w []
  have h := hcorrect (joinedBits x w) []
  simp only [Source284JoinedDecodeTM2.pairedRelation,hd] at h
  simpa only [verifier,Shared.Codes.FiniteProgramRepair.bounded_repair,guarded,
    Source284OriginalCutoffVerifier.guarded_correct] using h

end Shared.Beeping.NPcoNP.Source284JoinedFiniteVerifier
