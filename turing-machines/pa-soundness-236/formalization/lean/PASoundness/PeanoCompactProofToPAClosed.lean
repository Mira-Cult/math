import PASoundness.PeanoAX8Comprehension
import PASoundness.PeanoPowerGrowth

/-! Unconditional compact-to-PA derivation transport and its truth map.

The literal AX8 PA derivations discharge the last premise of the existing
finite logical transport. This file does not derive PA-to-compact proof
transport or a machine/soundness equivalence. PA derivability is Prop-valued;
these interfaces do not claim an executable PA proof-tree extractor.
-/
namespace PASoundness.PeanoCompactProofToPAClosed
open FirstOrder FirstOrder.Language
open Peano CompactProof CompactArithmetic CompactLogicalTransport

/-- Every data-valued compact derivation gives a PA derivation of its literal
open arithmetic translation. No semantic soundness is used in this direction. -/
theorem derivation_to_pa {f : Nat} (d : KDerivation f) :
    FormulaProves (interpreted f) :=
  CompactLogicalTransport.derivation_transport_from_comprehension
    PeanoPowerGrowth.translated_bottom PeanoAX8Comprehension.comprehension d

/-- Grounding the same translated proof yields the existing closed PA
sentence associated with the compact numeric formula. -/
theorem proof_to_pa {f : Nat} (d : KDerivation f) :
    Peano.Proves (toPA f) :=
  PeanoPowerGrowth.proofToPA_of_comprehension PeanoAX8Comprehension.comprehension d

/-- The Prop-valued compact provability interface also transports to PA. -/
theorem provability_to_pa {f : Nat} (h : KProves f) :
    Peano.Proves (toPA f) := by
  obtain ⟨d⟩ := h
  exact proof_to_pa d

/-- Every numeric source certificate has a compact derivation and hence its
literal interpreted theorem has a PA derivation. -/
theorem theorem_code_to_pa (code : Nat) :
    Peano.Proves (toPA (theoremCode code)) :=
  provability_to_pa (theorem_origin code)

/-- The corresponding open arithmetic translation preserves and reflects
truth for every numeric code and every standard assignment. This semantic
equivalence is separate from the proof derivation above. -/
theorem translation_truth (code : Nat) (ρ : Nat → Nat) :
    (interpreted code).Realize ρ ↔ (CompactMatrix.decode code).Realize ρ :=
  CompactArithmetic.realize_translate _ _

/-- The existing grounded sentence has the same standard truth value as the
compact formula at the all-zero assignment. -/
theorem sentence_truth (code : Nat) :
    (Nat ⊨ toPA code) ↔ (CompactMatrix.decode code).Realize (fun _ => 0) :=
  CompactArithmetic.truth_toPA code

end PASoundness.PeanoCompactProofToPAClosed

#print axioms PASoundness.PeanoCompactProofToPAClosed.derivation_to_pa
#print axioms PASoundness.PeanoCompactProofToPAClosed.proof_to_pa
#print axioms PASoundness.PeanoCompactProofToPAClosed.theorem_code_to_pa
#print axioms PASoundness.PeanoCompactProofToPAClosed.translation_truth
#print axioms PASoundness.PeanoCompactProofToPAClosed.sentence_truth
