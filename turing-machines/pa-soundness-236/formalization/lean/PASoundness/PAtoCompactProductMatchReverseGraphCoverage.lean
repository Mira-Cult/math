import PASoundness.PAtoCompactProductMatchGraphOrder
import PASoundness.PAtoCompactProductMatchReverseTotalityRetained

/-! Reverse coverage of the supplied guarded match graph. Both product
matrices, both factor bijections, the graph invariant, and target membership
are explicit antecedents. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchReverseGraphCoverage

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductMatchTargetOutput PASoundness.PAtoCompactProductMatchRelation
open PASoundness.PAtoCompactProductMatchPartialBase PASoundness.PAtoCompactProductMatchGraphOrder
open PASoundness.PAtoCompactProductMatchReverseReconstruct PASoundness.PAtoCompactProductMatchReverseTotality
open PASoundness.PAtoCompactProductMatchReverseRetainedSource PASoundness.PAtoCompactProductMatchReverseTotalityRetained
open PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactFreeVacuity

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def queryPoint : Formula := replace 57 55 (replace 56 32 matchPoint)
def graphGuard : Formula := namedBoth actualMatch (.member 44 55)
def graphResult : Formula := namedBoth (.member 2 32) (graphFormula 58 32 55)

theorem query_shape : queryPoint = .imp (namedBoth (.member 2 32) (.member 44 55))
    (namedBoth (.imp (graphFormula 58 32 55) (namedBoth (.member 2 32) (replace 35 55 path)))
      (.imp (namedBoth (.member 2 32) (replace 35 55 path)) (graphFormula 58 32 55))) := by decide

def query_instance : KDerivation (imp actualMatch.encode queryPoint.encode) := by
  have h56 := universalInstance 56 32 (.all 57 matchPoint) (by decide) (by decide) (by decide)
  have hs : replace 56 32 (.all 57 matchPoint) = .all 57 (replace 56 32 matchPoint) := by decide
  rw [hs] at h56
  have h57 := universalInstance 57 55 (replace 56 32 matchPoint) (by decide) (by decide) (by decide)
  rw [actual_match_shape]
  simpa [queryPoint, Formula.encode] using compose h56 h57

/-- A retained body gives a graph edge, preserving source membership. -/
def body_to_graph : KDerivation
    (imp graphGuard.encode (imp retainedSourceBody.encode graphResult.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [retainedSourceBody.encode, graphGuard.encode]
  have hb : Context Γ retainedSourceBody.encode := .head _ _
  have hg : Context Γ graphGuard.encode := .hypothesis (by simp [Γ])
  have hb' : Context Γ (both (member 2 32) pathBody55.encode) := by
    simpa [retainedSourceBody, namedBoth, Formula.not, Formula.encode, both, neg] using hb
  have hg' : Context Γ (both actualMatch.encode (member 44 55)) := by
    simpa [graphGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have hm := Context.conjunctionLeft hb'
  have hp := Context.conjunctionRight hb'
  have h34 := Context.mp hp (.closed (existsIntroduce 34 pathBody55 (by decide)))
  have h33 := Context.mp h34 (.closed (existsIntroduce 33 (.ex 34 pathBody55) (by decide)))
  have h31 := Context.mp h33 (.closed (existsIntroduce 31 (.ex 33 (.ex 34 pathBody55)) (by decide)))
  have h30 := Context.mp h31 (.closed (existsIntroduce 30 (.ex 31 (.ex 33 (.ex 34 pathBody55))) (by decide)))
  have hpath : Context Γ (replace 35 55 path).encode := by
    simpa [path_at_55_shape, Formula.encode] using h30
  have hq := Context.mp (Context.conjunctionLeft hg') (.closed query_instance)
  have hq' : Context Γ (imp (both (member 2 32) (member 44 55))
      (both (imp (graphFormula 58 32 55).encode (both (member 2 32) (replace 35 55 path).encode))
        (imp (both (member 2 32) (replace 35 55 path).encode) (graphFormula 58 32 55).encode))) := by
    simpa [query_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hq
  have hpair := Context.conjunctionIntro hm (Context.conjunctionRight hg')
  have hedge := Context.mp (Context.conjunctionIntro hm hpath)
    (Context.conjunctionRight (Context.mp hpair hq'))
  simpa [Γ, graphResult, namedBoth, Formula.not, Formula.encode, both, neg] using
    Context.conjunctionIntro hm hedge

/-- Eliminate the four private path witnesses while keeping the output 32. -/
def witnesses_to_graph : KDerivation
    (imp graphGuard.encode (imp (existsCode 30 (existsCode 31 (existsCode 33
      (existsCode 34 retainedSourceBody.encode)))) graphResult.encode)) := by
  have h34 := guarded_exists_left 34 graphGuard.encode retainedSourceBody.encode graphResult.encode
    (free_vacuity 34 graphGuard (by decide)) (graphResult.vacuity 34 (by decide)) body_to_graph
  have h33 := guarded_exists_left 33 graphGuard.encode (existsCode 34 retainedSourceBody.encode) graphResult.encode
    (free_vacuity 33 graphGuard (by decide)) (graphResult.vacuity 33 (by decide)) h34
  have h31 := guarded_exists_left 31 graphGuard.encode (existsCode 33 (existsCode 34 retainedSourceBody.encode)) graphResult.encode
    (free_vacuity 31 graphGuard (by decide)) (graphResult.vacuity 31 (by decide)) h33
  exact guarded_exists_left 30 graphGuard.encode (existsCode 31 (existsCode 33 (existsCode 34 retainedSourceBody.encode))) graphResult.encode
    (free_vacuity 30 graphGuard (by decide)) (graphResult.vacuity 30 (by decide)) h31

/-- Every target product member has a source member connected by this graph. -/
def reverse_graph_coverage : KDerivation (imp productMatrix.encode (imp firstBijection.encode
    (imp secondBijection.encode (imp targetMatrix.encode (imp actualMatch.encode
      (imp (member 44 55) (existsCode 32 graphResult.encode))))))) := by
  have hlift := conditionalExistsCongr 32 (graphGuard.vacuity 32 (by decide)) witnesses_to_graph
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 44 55,actualMatch.encode,targetMatrix.encode,secondBijection.encode,
    firstBijection.encode,productMatrix.encode]
  have hy : Context Γ (member 44 55) := .head _ _
  have ha : Context Γ actualMatch.encode := .hypothesis (by simp [Γ])
  have ht : Context Γ targetMatrix.encode := .hypothesis (by simp [Γ])
  have hb₂ : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hb₁ : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ productMatrix.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ graphGuard.encode := by
    simpa [graphGuard, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionIntro ha hy
  have hw := Context.mp hy (Context.mp ht (Context.mp hb₂ (Context.mp hb₁
    (Context.mp hp (.closed reverse_total_retaining_source)))))
  simpa [Γ] using Context.mp hw (Context.mp hg (.closed hlift))

theorem reverse_graph_coverage_certificate : theoremCode (certificate reverse_graph_coverage) =
    imp productMatrix.encode (imp firstBijection.encode (imp secondBijection.encode
      (imp targetMatrix.encode (imp actualMatch.encode
        (imp (member 44 55) (existsCode 32 graphResult.encode)))))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchReverseGraphCoverage

#print axioms PASoundness.PAtoCompactProductMatchReverseGraphCoverage.query_instance
#print axioms PASoundness.PAtoCompactProductMatchReverseGraphCoverage.body_to_graph
#print axioms PASoundness.PAtoCompactProductMatchReverseGraphCoverage.witnesses_to_graph
#print axioms PASoundness.PAtoCompactProductMatchReverseGraphCoverage.reverse_graph_coverage
#print axioms PASoundness.PAtoCompactProductMatchReverseGraphCoverage.reverse_graph_coverage_certificate
