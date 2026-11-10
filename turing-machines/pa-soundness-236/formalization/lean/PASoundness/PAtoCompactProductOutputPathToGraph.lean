import PASoundness.PAtoCompactProductOutputSameSourceTriple
import PASoundness.PAtoCompactProductOutputTripleExtension
import PASoundness.PAtoCompactProductOutputOutsideStep
import PASoundness.PAtoCompactTransitiveClosure
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactSuccGraphOutputLift

/-! Guarded reverse coverage for one single-triple extension. A path in the
successor prefix uses either the selected source endpoint or the old prefix;
the chosen new graph retains old triples and contains the selected triple. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputPathToGraph

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactSuccessorInjective
open PASoundness.PAtoCompactSuccGraphOutputLift PASoundness.PAtoCompactMultiplicationSingleTripleExtension
open PASoundness.PAtoCompactProductOutputPartialBase PASoundness.PAtoCompactProductOutputOutsidePath
open PASoundness.PAtoCompactProductOutputOutsidePathLift PASoundness.PAtoCompactProductOutputOutsideStep
open PASoundness.PAtoCompactProductOutputInsideSelected PASoundness.PAtoCompactProductOutputTripleExtension
open PASoundness.PAtoCompactProductOutputSameSourceTriple

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def coverageGuard : Formula := namedBoth relocatedBody (namedBoth (namedSuccessor 74 59 76)
  (namedBoth oldInvariant (namedBoth selectedTriple newRetained)))
def guardedQuery : Formula := namedBoth coverageGuard endpointGuard

def oldTriple : Formula := tripleAt 58 56 57 60
def newTriple : Formula := tripleAt 9 56 57 60

theorem retained_shape : newRetained = .all 3 (.all 4 (.all 5
    (.imp (tripleAt 58 3 4 5) (tripleAt 9 3 4 5)))) := by decide

def retained_instance : KDerivation (imp newRetained.encode (imp oldTriple.encode newTriple.encode)) := by
  let F : Formula := .imp (tripleAt 58 3 4 5) (tripleAt 9 3 4 5)
  have h3 := universalInstance 3 56 (.all 4 (.all 5 F)) (by decide) (by decide) (by decide)
  have hs3 : replace 3 56 (.all 4 (.all 5 F)) = .all 4 (.all 5 (replace 3 56 F)) := by decide
  rw [hs3] at h3
  have h4 := universalInstance 4 57 (.all 5 (replace 3 56 F)) (by decide) (by decide) (by decide)
  have hs4 : replace 4 57 (.all 5 (replace 3 56 F)) = .all 5 (replace 4 57 (replace 3 56 F)) := by decide
  rw [hs4] at h4
  have h5 := universalInstance 5 60 (replace 4 57 (replace 3 56 F)) (by decide) (by decide) (by decide)
  have hs5 : replace 5 60 (replace 4 57 (replace 3 56 F)) = .imp oldTriple newTriple := by decide
  rw [hs5] at h5
  simpa [retained_shape, F, CompactNamed.Formula.encode] using compose h3 (compose h4 h5)

/-- For a fixed path witness 32, split its successor membership into selected
endpoint versus old prefix and retain the same payload in either branch. -/
def path_body_to_graph : KDerivation (imp guardedQuery.encode (imp bodyAt.encode newTriple.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [bodyAt.encode,guardedQuery.encode]
  have hb : Context Γ bodyAt.encode := .head _ _
  have hg : Context Γ guardedQuery.encode := .hypothesis (by simp [Γ])
  have hb0 : Context Γ nextBody.encode := by
    rw [next_body_shape]
    exact hb
  have hb' : Context Γ (both (member 59 32) payloadAt.encode) := by
    simpa [nextBody, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using hb0
  have hg' : Context Γ (both coverageGuard.encode endpointGuard.encode) := by
    simpa [guardedQuery, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hg
  have hc : Context Γ (both relocatedBody.encode (both (successorCode 74 59 76)
      (both oldInvariant.encode (both selectedTriple.encode newRetained.encode)))) := by
    simpa [coverageGuard, namedSuccessor, namedSuccessorBody, successorCode, namedBoth, namedEither,
      CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, either] using Context.conjunctionLeft hg'
  have hsel := Context.conjunctionLeft hc
  have hsucc := Context.conjunctionLeft (Context.conjunctionRight hc)
  have hold := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hc))
  have htri := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hc)))
  have hret := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hc)))
  have hend := Context.conjunctionRight hg'
  have hpay := Context.conjunctionRight hb'
  have hsplit := Context.mp (Context.conjunctionLeft hb') (Context.mp hsucc
    (.closed (successor_inspect 74 59 76 32 (by decide) (by decide) (by decide))))
  apply Context.disjunctionElim hsplit
  · let Δ := equal 32 74 :: Γ
    have he : Context Δ (equal 32 74) := .head _ _
    have hs : Context Δ sameSourceGuard.encode := by
      simpa [sameSourceGuard, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
        Context.conjunctionIntro (.under hsel _) (Context.conjunctionIntro (.under hend _) (.under htri _))
    simpa [newTriple, queriedTriple] using Context.mp (.under hpay _)
      (Context.mp he (Context.mp hs (.closed same_source_triple)))
  · let Δ := member 74 32 :: Γ
    have hm : Context Δ (member 74 32) := .head _ _
    have hbody : Context Δ oldBody.encode := by
      simpa [oldBody, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
        Context.conjunctionIntro hm (.under hpay _)
    have hi := existsIntroduce 32 oldBody (by decide)
    have hpath : Context Δ oldPath.encode := by
      simpa [oldPath, CompactNamed.Formula.encode] using Context.mp hbody (.closed hi)
    have hold' : Context Δ oldInvariant.encode := .under hold (member 74 32)
    have hpnt : Context Δ oldPoint.encode := .mp hold' (.closed old_instance)
    have hboth : Context Δ (both (imp oldTriple.encode oldPath.encode)
        (imp oldPath.encode oldTriple.encode)) := by
      simpa [oldPoint, oldTriple, targetTriple, namedBoth, CompactNamed.Formula.not,
        CompactNamed.Formula.encode, both, neg] using Context.mp (.under hend _) hpnt
    have htold := Context.mp hpath (Context.conjunctionRight hboth)
    exact .mp htold (.mp (.under hret _) (.closed retained_instance))

/-- Every path of the successor prefix yields a triple in this same new
graph, under the literal selected/retained triple and old-invariant guards. -/
def path_to_graph : KDerivation (imp coverageGuard.encode (imp endpointGuard.encode
    (imp pathAt.encode newTriple.encode))) := by
  have helim := guarded_exists_left 32 guardedQuery.encode bodyAt.encode newTriple.encode
    (free_vacuity 32 guardedQuery (by decide)) (newTriple.vacuity 32 (by decide)) path_body_to_graph
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [pathAt.encode,endpointGuard.encode,coverageGuard.encode]
  have hp : Context Γ pathAt.encode := .head _ _
  have he : Context Γ endpointGuard.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ coverageGuard.encode := .hypothesis (by simp [Γ])
  have hq : Context Γ guardedQuery.encode := by
    simpa [guardedQuery, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
      Context.conjunctionIntro hg he
  have hp' : Context Γ (existsCode 32 bodyAt.encode) := by
    simpa [path_at_shape, CompactNamed.Formula.encode] using hp
  exact .mp hp' (.mp hq (.closed helim))

theorem path_to_graph_certificate : theoremCode (certificate path_to_graph) =
    imp coverageGuard.encode (imp endpointGuard.encode (imp pathAt.encode newTriple.encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputPathToGraph

#print axioms PASoundness.PAtoCompactProductOutputPathToGraph.retained_instance
#print axioms PASoundness.PAtoCompactProductOutputPathToGraph.path_body_to_graph
#print axioms PASoundness.PAtoCompactProductOutputPathToGraph.path_to_graph
#print axioms PASoundness.PAtoCompactProductOutputPathToGraph.path_to_graph_certificate
