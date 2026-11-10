import PASoundness.PAtoCompactMultiplicationReverseWitnessLift
import PASoundness.PAtoCompactMultiplicationSuffixCompetitorQuantify
import PASoundness.PAtoCompactMultiplicationCandidate

/-! Given a pointwise finite K competitor-reflection proof, quantify it and
attach it to the same retained product preimage. The retained preimage carries
its chosen suffix-map edge, so this does not assume that the edge can be
reconstructed from the weaker reverse formula. Reflection and preimage
existence remain explicit inputs; no multiplication totality is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationReverseWitnessFromPoint
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationSuffixReverseExistence
open PASoundness.PAtoCompactMultiplicationReverseWitnessLift
open PASoundness.PAtoCompactMultiplicationSuffixCompetitorQuantify
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The exact renamed product reverse witness body. -/
def targetBody : Formula := reverseBody uniqueBody

/-- The exact renamed reverse clause of the original product matrix. -/
theorem reverse_clause_syntax :
    replace 6 64 (replace 2 45 (replace 1 31 (replace 0 38 reverseFormula))) =
      .all 5 (.imp (.member 45 5) (.ex 3 (.ex 4 targetBody))) := by decide

/-- A supplied pointwise reflection proof strengthens the same retained
primary witnesses to the exact reverse-clause body. All four free-name
conditions refer only to the ambient context H; the primary retains F(4,5).
Neither reflection nor existence is supplied by this constructor. -/
def reverse_witness_from_point (H : Formula)
    (h3 : 3 ∉ H.free) (h4 : 4 ∉ H.free) (h7 : 7 ∉ H.free) (h8 : 8 ∉ H.free)
    (hpoint : KDerivation (pointCode H)) :
    KDerivation (imp H.encode (imp (existsCode 3 (existsCode 4 primary.encode))
      (existsCode 3 (existsCode 4 targetBody.encode)))) := by
  have hproj : KDerivation (imp primary.encode (reversePreimageBody 3 4).encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hp : Context [primary.encode] primary.encode := .head _ _
    change Context [primary.encode] (both (reversePreimageBody 3 4).encode
      (graphFormula 6 4 5).encode) at hp
    exact Context.conjunctionLeft hp
  exact strengthen_preimage H primary uniqueBody h3 h4 hproj (quantify H h7 h8 hpoint)

theorem reverse_witness_from_point_certificate (H : Formula)
    (h3 : 3 ∉ H.free) (h4 : 4 ∉ H.free) (h7 : 7 ∉ H.free) (h8 : 8 ∉ H.free)
    (hpoint : KDerivation (pointCode H)) :
    theoremCode (certificate (reverse_witness_from_point H h3 h4 h7 h8 hpoint)) =
      imp H.encode (imp (existsCode 3 (existsCode 4 primary.encode))
        (existsCode 3 (existsCode 4 targetBody.encode))) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationReverseWitnessFromPoint
#print axioms PASoundness.PAtoCompactMultiplicationReverseWitnessFromPoint.reverse_clause_syntax
#print axioms PASoundness.PAtoCompactMultiplicationReverseWitnessFromPoint.reverse_witness_from_point
#print axioms PASoundness.PAtoCompactMultiplicationReverseWitnessFromPoint.reverse_witness_from_point_certificate
