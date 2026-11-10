import PASoundness.PAtoCompactPAAddZeroAxiomClosed
import PASoundness.PAtoCompactPAAddZeroNecessity

/-! Exact finite-K reduction for the guarded PA addition-zero axiom.
The equivalence concerns the existence of proof data; it is not an appeal to
semantic soundness or to a metatheoretic proof of either statement. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PASoundness.PAtoCompactPAAddZeroEquivalence

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactUnaryGuardedCanonical

/-- The exact guarded canonical graph-existence code needed for the argument
of the translated addition-zero axiom. -/
def childCode (t : Peano.Term) : Nat :=
  let A := (Peano.add t Peano.zero).equal t
  imp (guardFormula A).encode
    (existsCode (outputName A) (termGraph id t (outputName A) (allocatorBase A)).encode)

/-- Graph existence and the actual guarded addition-zero axiom give finite K
proofs of one another, uniformly for arbitrary PA terms. -/
noncomputable def proofTransforms (t : Peano.Term) :
    (KDerivation (childCode t) →
      KDerivation (guardedCode ((Peano.add t Peano.zero).equal t))) ×
    (KDerivation (guardedCode ((Peano.add t Peano.zero).equal t)) →
      KDerivation (childCode t)) := by
  constructor
  · intro h
    apply PASoundness.PAtoCompactPAAddZeroAxiomClosed.add_zero_of_child t
    simpa [childCode, outputName, allocatorBase] using h
  · intro h
    simpa [childCode] using PASoundness.PAtoCompactPAAddZeroNecessity.guarded_graph_of_add_zero t h

/-- Existence of a finite K proof is equivalent for the two literal codes. -/
theorem derivation_exists_iff (t : Peano.Term) :
    Nonempty (KDerivation (childCode t)) ↔
      Nonempty (KDerivation (guardedCode ((Peano.add t Peano.zero).equal t))) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨(proofTransforms t).1 h⟩
  · rintro ⟨h⟩
    exact ⟨(proofTransforms t).2 h⟩

end PASoundness.PAtoCompactPAAddZeroEquivalence

#print axioms PASoundness.PAtoCompactPAAddZeroEquivalence.proofTransforms
#print axioms PASoundness.PAtoCompactPAAddZeroEquivalence.derivation_exists_iff
