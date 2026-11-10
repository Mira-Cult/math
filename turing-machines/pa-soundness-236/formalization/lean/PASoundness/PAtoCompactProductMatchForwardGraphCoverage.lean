import PASoundness.PAtoCompactProductMatchGraphOrder
import PASoundness.PAtoCompactProductMatchSourceWitness

/-! Pointwise source coverage for a supplied product-match graph, with the
selected target membership and graph edge on the same witness. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchForwardGraphCoverage

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductMatchTargetOutput PASoundness.PAtoCompactProductMatchTargetWitness
open PASoundness.PAtoCompactProductMatchPointWitness
open PASoundness.PAtoCompactProductMatchSourceWitness PASoundness.PAtoCompactProductMatchBothImages
open PASoundness.PAtoCompactProductMatchRelation PASoundness.PAtoCompactProductMatchGraphOrder
open PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactFreeVacuity

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def forwardGuard : Formula := namedBoth actualMatch (.member 2 32)
def forwardResult : Formula := namedBoth (.member 44 35) (graphFormula 58 32 35)

def body_to_graph : KDerivation
    (imp forwardGuard.encode (imp retainedMatchBody.encode forwardResult.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [retainedMatchBody.encode,forwardGuard.encode]
  have hb : Context Γ retainedMatchBody.encode := .head _ _
  have hg : Context Γ forwardGuard.encode := .hypothesis (by simp [Γ])
  have hg' : Context Γ (both actualMatch.encode (member 2 32)) := by
    simpa [forwardGuard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
  have hb' : Context Γ (both selectedReverseBody.encode
      (both bothImages.encode targetOutputBody.encode)) := by
    simpa [retainedMatchBody, matchBody, namedBoth, Formula.not, Formula.encode, both, neg] using hb
  have ht := Context.conjunctionRight (Context.conjunctionRight hb')
  have ht' : Context Γ (both (member 44 35) (both (targetTriple 33 34 35).encode
      (Formula.all 9 (.imp (namedBoth (.member 44 9) (targetTriple 33 34 9)) (.equal 9 35))).encode)) := by
    simpa [targetOutputBody, namedBoth, Formula.not, Formula.encode, both, neg] using ht
  have hy := Context.conjunctionLeft ht'
  have hx := Context.conjunctionRight hg'
  have h34 := Context.mp hb (.closed (existsIntroduce 34 retainedMatchBody (by decide)))
  have h33 := Context.mp h34 (.closed (existsIntroduce 33 (.ex 34 retainedMatchBody) (by decide)))
  have h31 := Context.mp h33 (.closed (existsIntroduce 31 (.ex 33 (.ex 34 retainedMatchBody)) (by decide)))
  have h30 := Context.mp h31 (.closed (existsIntroduce 30 (.ex 31 (.ex 33 (.ex 34 retainedMatchBody))) (by decide)))
  have hpath : Context Γ path.encode := by simpa [path, Formula.encode] using h30
  have hq := Context.mp (Context.conjunctionLeft hg') (.closed first_instance)
  have hq' : Context Γ (imp (both (member 2 32) (member 44 35))
      (both (imp (graphFormula 58 32 35).encode (both (member 2 32) path.encode))
        (imp (both (member 2 32) path.encode) (graphFormula 58 32 35).encode))) := by
    simpa [first_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hq
  have hedge := Context.mp (Context.conjunctionIntro hx hpath)
    (Context.conjunctionRight (Context.mp (Context.conjunctionIntro hx hy) hq'))
  simpa [Γ, forwardResult, namedBoth, Formula.not, Formula.encode, both, neg] using
    Context.conjunctionIntro hy hedge

def path_to_graph : KDerivation (imp forwardGuard.encode (imp path.encode forwardResult.encode)) := by
  have h34 := guarded_exists_left 34 forwardGuard.encode retainedMatchBody.encode forwardResult.encode
    (free_vacuity 34 forwardGuard (by decide)) (forwardResult.vacuity 34 (by decide)) body_to_graph
  have h33 := guarded_exists_left 33 forwardGuard.encode (existsCode 34 retainedMatchBody.encode) forwardResult.encode
    (free_vacuity 33 forwardGuard (by decide)) (forwardResult.vacuity 33 (by decide)) h34
  have h31 := guarded_exists_left 31 forwardGuard.encode (existsCode 33 (existsCode 34 retainedMatchBody.encode)) forwardResult.encode
    (free_vacuity 31 forwardGuard (by decide)) (forwardResult.vacuity 31 (by decide)) h33
  have h30 := guarded_exists_left 30 forwardGuard.encode (existsCode 31 (existsCode 33 (existsCode 34 retainedMatchBody.encode))) forwardResult.encode
    (free_vacuity 30 forwardGuard (by decide)) (forwardResult.vacuity 30 (by decide)) h31
  simpa [path, Formula.encode] using h30

def forward_graph_coverage : KDerivation (imp productMatrix.encode (imp firstBijection.encode
    (imp secondBijection.encode (imp targetMatrix.encode (imp actualMatch.encode
      (imp (member 2 32) (existsCode 35 forwardResult.encode))))))) := by
  have hlift := conditionalExistsCongr 35 (forwardGuard.vacuity 35 (by decide)) path_to_graph
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 2 32,actualMatch.encode,targetMatrix.encode,secondBijection.encode,
    firstBijection.encode,productMatrix.encode]
  have hx : Context Γ (member 2 32) := .head _ _
  have ha : Context Γ actualMatch.encode := .hypothesis (by simp [Γ])
  have ht : Context Γ targetMatrix.encode := .hypothesis (by simp [Γ])
  have hb₂ : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hb₁ : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ productMatrix.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ forwardGuard.encode := by
    simpa [forwardGuard, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionIntro ha hx
  have hw := Context.mp ht (Context.mp hb₂ (Context.mp hb₁ (Context.mp hx
    (Context.mp hp (.closed path_exists)))))
  simpa [Γ] using Context.mp hw (Context.mp hg (.closed hlift))

theorem forward_graph_coverage_certificate : theoremCode (certificate forward_graph_coverage) =
    imp productMatrix.encode (imp firstBijection.encode (imp secondBijection.encode
      (imp targetMatrix.encode (imp actualMatch.encode
        (imp (member 2 32) (existsCode 35 forwardResult.encode)))))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchForwardGraphCoverage

#print axioms PASoundness.PAtoCompactProductMatchForwardGraphCoverage.body_to_graph
#print axioms PASoundness.PAtoCompactProductMatchForwardGraphCoverage.path_to_graph
#print axioms PASoundness.PAtoCompactProductMatchForwardGraphCoverage.forward_graph_coverage
#print axioms PASoundness.PAtoCompactProductMatchForwardGraphCoverage.forward_graph_coverage_certificate
