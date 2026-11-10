import PASoundness.PAtoCompactProductOutputTripleNoGarbage
import PASoundness.PAtoCompactProductOutputSelectedPathAtQuery
import PASoundness.PAtoCompactProductOutputOldPathLift
import PASoundness.PAtoCompactProductOutputOutsideStep

/-! Guarded forward coverage for a single adjoined target-product triple:
a queried new triple has a path in the successor prefix. The reverse
coverage and the quantified partial graph invariant remain separate. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputGraphToPath

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactMultiplicationSingleTripleExtension
open PASoundness.PAtoCompactProductOutputPartialBase PASoundness.PAtoCompactProductOutputOutsidePathLift
open PASoundness.PAtoCompactProductOutputOutsideStep PASoundness.PAtoCompactProductOutputInsideSelected
open PASoundness.PAtoCompactProductOutputSelectedPath PASoundness.PAtoCompactProductOutputSelectedPathAtQuery
open PASoundness.PAtoCompactProductOutputOldPathLift PASoundness.PAtoCompactProductOutputTripleNoGarbage

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def stepGuard : Formula := namedBoth relocatedBody (namedBoth (namedSuccessor 74 59 76)
  (namedBoth PAtoCompactProductOutputTripleNoGarbage.guard oldInvariant))
def newTriple : Formula := tripleAt 9 56 57 60

/-- From a queried new triple, use the old invariant in the old branch and
retarget the selected path in the new branch. -/
def graph_to_path : KDerivation (imp stepGuard.encode (imp endpointGuard.encode
    (imp newTriple.encode pathAt.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [newTriple.encode,endpointGuard.encode,stepGuard.encode]
  have ht : Context Γ newTriple.encode := .head _ _
  have he : Context Γ endpointGuard.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ stepGuard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both relocatedBody.encode (both (successorCode 74 59 76)
      (both PAtoCompactProductOutputTripleNoGarbage.guard.encode oldInvariant.encode))) := by
    simpa [stepGuard, namedSuccessor, namedSuccessorBody, successorCode, namedBoth, namedEither,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, either] using hg
  have hsel := Context.conjunctionLeft hg'
  have hsucc := Context.conjunctionLeft (Context.conjunctionRight hg')
  have hng := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hg'))
  have hold := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg'))
  have hsplit : Context Γ (either targetTriple.encode equalities.encode) := by
    simpa [newTriple, targetTriple, result, namedEither, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, either, neg] using
        (Context.mp ht (Context.mp hng (.closed triple_no_garbage)))
  apply Context.disjunctionElim hsplit
  · let Δ := targetTriple.encode :: Γ
    have htold : Context Δ targetTriple.encode := .head _ _
    have he' : Context Δ endpointGuard.encode := .under he _
    have hold' : Context Δ oldInvariant.encode := .under hold _
    have hsucc' : Context Δ (successorCode 74 59 76) := .under hsucc _
    have hpoint := Context.mp hold' (.closed old_instance)
    have hequiv : Context Δ (both (imp targetTriple.encode oldPath.encode)
        (imp oldPath.encode targetTriple.encode)) := by
      simpa [oldPoint, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode,
        both, neg] using Context.mp he' hpoint
    have hpath := Context.mp htold (Context.conjunctionLeft hequiv)
    exact .mp hpath (.mp hsucc' (.closed old_path_lift))
  · let Δ := equalities.encode :: Γ
    have heq : Context Δ equalities.encode := .head _ _
    have heq' : Context Δ (both (equal 56 30) (both (equal 57 31) (equal 60 33))) := by
      simpa [equalities, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using heq
    have hsel' : Context Δ relocatedBody.encode := .under hsel _
    have hsucc' : Context Δ (successorCode 74 59 76) := .under hsucc _
    have hpath := Context.mp hsel' (Context.mp hsucc' (.closed selected_path))
    exact .mp hpath (.mp (Context.conjunctionRight (Context.conjunctionRight heq'))
      (.mp (Context.conjunctionLeft (Context.conjunctionRight heq'))
        (.mp (Context.conjunctionLeft heq') (.closed selected_path_at_query))))

theorem graph_to_path_certificate : theoremCode (certificate graph_to_path) =
    imp stepGuard.encode (imp endpointGuard.encode (imp newTriple.encode pathAt.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputGraphToPath

#print axioms PASoundness.PAtoCompactProductOutputGraphToPath.graph_to_path
#print axioms PASoundness.PAtoCompactProductOutputGraphToPath.graph_to_path_certificate
