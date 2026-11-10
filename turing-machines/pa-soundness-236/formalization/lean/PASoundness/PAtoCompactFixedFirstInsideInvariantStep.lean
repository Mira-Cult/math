import PASoundness.PAtoCompactFixedFirstInsideSyntax
import PASoundness.PAtoCompactFixedFirstInsideCoverage11
import PASoundness.PAtoCompactFixedFirstTopCoverageAlignment
import PASoundness.PAtoCompactFixedFirstSuccessorProjection

/-! Literal finite K assembly of the inside-index successor step for the
fixed-first multiplication row invariant. The successor, old invariant,
adjunction, map edge, pair witnesses and top coverage are supplied as explicit
object-level antecedents. No row collection or multiplication totality is
claimed and no uniqueness of pair representatives is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstInsideInvariantStep
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactFixedFirstPreservedBase PASoundness.PAtoCompactFixedFirstInsideSyntax
open PASoundness.PAtoCompactFixedFirstInsideCoverage11 PASoundness.PAtoCompactFixedFirstTopCoverageEleven
open PASoundness.PAtoCompactFixedFirstTopCoverageAlignment PASoundness.PAtoCompactFixedFirstSuccessorProjection
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The complete invariant transfers through one inside-index extension,
retaining the supplied graph and pair witnesses literally. -/
def inside_invariant : KDerivation (imp (successorCode 0 1 2)
    (imp (member 31 0)
      (imp (rowInvariantPreserved 7).encode
        (imp (namedAdjoin 7 13 11 14).encode
          (imp (graphFormula 6 0 4).encode
            (imp (pairFormula 12 30 0).encode
              (imp (pairFormula 13 12 4).encode
                (imp topCoverage11.encode
                  (replace 0 1 (rowInvariantPreserved 11)).encode)))))))) := by
  let S := successorCode 0 1 2
  let Y := member 31 0
  let O := (rowInvariantPreserved 7).encode
  let A := (namedAdjoin 7 13 11 14).encode
  let F := (graphFormula 6 0 4).encode
  let P := (pairFormula 12 30 0).encode
  let Q := (pairFormula 13 12 4).encode
  let T := topCoverage11.encode
  let Γ := [T,Q,P,F,A,O,Y,S]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hy : Context Γ Y := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hq : Context Γ Q := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .head _ _
  have hconj : Context Γ (both (oldPreserved 7).encode
      (both (coverage 7).encode (noGarbage 7).encode)) := by
    simpa [O,rowInvariantPreserved,rowInvariant,namedBoth,Formula.not,Formula.encode,both,neg] using ho
  have hpres : Context Γ (oldPreserved 7).encode := Context.conjunctionLeft hconj
  have hcov : Context Γ (coverage 7).encode := Context.conjunctionLeft (Context.conjunctionRight hconj)
  have hng : Context Γ (noGarbage 7).encode := Context.conjunctionRight (Context.conjunctionRight hconj)
  have hpres' : Context Γ (oldPreserved 11).encode := by
    have h := Context.mp hpres (Context.mp ha (.closed PAtoCompactMultiplicationOldGraphAtEleven.old_preserved_at_eleven))
    simpa only [preservation_agrees] using h
  have hcov11 : Context Γ (coverage 11).encode := by
    have h := Context.mp hcov (Context.mp ha (.closed PAtoCompactMultiplicationRowCoverageAtEleven.coverage_all_preserved_at_eleven))
    simpa only [coverage_agrees] using h
  have htop : Context Γ topWitness11.encode := by simpa only [top_witness_alignment] using ht
  have hcov' : Context Γ (replace 0 1 (coverage 11)).encode :=
    .mp htop (.mp hcov11 (.mp hs (.closed inside_coverage11)))
  have hinc : Context Γ PAtoCompactMultiplicationRowPrefixTransport.prefixInclusion :=
    .mp hs (.closed successor_inclusion)
  have hend : Context Γ (member 1 0) := .mp hs (.closed successor_endpoint)
  have hng' : Context Γ PAtoCompactMultiplicationRowNoGarbageStep.newNoGarbage.encode := by
    have hold : Context Γ PAtoCompactMultiplicationRowOldEntry.oldNoGarbage.encode := by
      simpa only [old_no_garbage_agrees] using hng
    exact .mp hq (.mp hp (.mp hf (.mp hy (.mp hend (.mp ha (.mp hold (.mp hinc
      (.closed PAtoCompactMultiplicationRowNoGarbageStep.no_garbage_step))))))))
  have hc := Context.conjunctionIntro hpres' (Context.conjunctionIntro hcov' hng')
  have hresult : Context Γ (replace 0 1 (rowInvariantPreserved 11)).encode := by
    rw [new_invariant_shape]
    simpa [namedBoth,Formula.not,Formula.encode,both,neg] using hc
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hresult

theorem inside_invariant_certificate : theoremCode (certificate inside_invariant) =
    imp (successorCode 0 1 2) (imp (member 31 0)
      (imp (rowInvariantPreserved 7).encode (imp (namedAdjoin 7 13 11 14).encode
        (imp (graphFormula 6 0 4).encode (imp (pairFormula 12 30 0).encode
          (imp (pairFormula 13 12 4).encode (imp topCoverage11.encode
            (replace 0 1 (rowInvariantPreserved 11)).encode))))))) := certificate_correct inside_invariant
end PASoundness.PAtoCompactFixedFirstInsideInvariantStep
#print axioms PASoundness.PAtoCompactFixedFirstInsideInvariantStep.inside_invariant
#print axioms PASoundness.PAtoCompactFixedFirstInsideInvariantStep.inside_invariant_certificate
