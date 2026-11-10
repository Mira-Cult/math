import PASoundness.PAtoCompactProductMatchOutsideStep
import PASoundness.PAtoCompactProductMatchCollectionConditional

/-! Reduce the remaining candidate-induction step for product-match graph
collection to its inside-source successor branch. The actual source and target
product matrices and both factor-bijection matrices remain object-level
antecedents. The inside branch is explicit K proof data, not established here. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchCollectionInsideConditional

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactQuantifiedRefutation PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductMatchTargetOutput PASoundness.PAtoCompactProductMatchPartialBase
open PASoundness.PAtoCompactProductMatchOutsideStep PASoundness.PAtoCompactProductMatchInductionFixture
open PASoundness.PAtoCompactProductMatchCollectionConditional

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def assumptions : Formula := namedBoth productMatrix
  (namedBoth firstBijection (namedBoth secondBijection targetMatrix))

/-- The sole additional K proof-data input for the nonempty extension: when
the old prefix endpoint lies inside the source, extend the partial graph to
its successor while retaining the four concrete matrix assumptions. -/
def InsideStep : Type := KDerivation (imp assumptions.encode
  (imp (successorCode 74 59 76) (imp (member 2 74)
    (imp (replace 64 74 predicate).encode (replace 64 59 predicate).encode))))

/-- Classical source membership splits the successor step into the supplied
inside proof and the separately constructed outside proof. -/
def successor_of_inside (inside : InsideStep) : KDerivation
    (imp assumptions.encode (imp (successorCode 74 59 76)
      (imp (replace 64 74 predicate).encode (replace 64 59 predicate).encode))) := by
  let H := assumptions.encode
  let S := successorCode 74 59 76
  let X := member 2 74
  let P := (replace 64 74 predicate).encode
  let Q := (replace 64 59 predicate).encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [P,S,H]
  have hp : Context Γ P := .head _ _
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  have hex : Context Γ (either X (neg X)) := .closed (CompactHilbertBasis.identity (neg X))
  apply Context.disjunctionElim hex
  · let Δ := [X,P,S,H]
    have hx : Context Δ X := .head _ _
    have hp' : Context Δ P := .under hp X
    have hs' : Context Δ S := .under hs X
    have hh' : Context Δ H := .under hh X
    exact .mp hp' (.mp hx (.mp hs' (.mp hh' (.closed inside))))
  · let Δ := [neg X,P,S,H]
    have hn : Context Δ (neg X) := .head _ _
    have hp' : Context Δ P := .under hp (neg X)
    have hs' : Context Δ S := .under hs (neg X)
    exact .mp hp' (.mp hn (.mp hs' (.closed outside_predicate_step)))

/-- The supplied inside proof and the outside branch yield the exact global
step required by the candidate-induction fixture. -/
def global_step_of_inside (inside : InsideStep) :
    KDerivation (imp assumptions.encode globalStep) := by
  let H := assumptions.encode
  let P := (replace 64 74 predicate).encode
  let Q := (replace 64 59 predicate).encode
  let S := successorCode 74 59 76
  let C := predecessorCore 71 74 59 76 77 78
  let Γ := [H]
  have hh : Context Γ H := .head _ _
  have hs : Context Γ (imp S (imp P Q)) := .mp hh (.closed (successor_of_inside inside))
  have hp : Context Γ (imp C (imp P Q)) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := [P,C,H]
    have hP : Context Δ P := .head _ _
    have hC : Context Δ C := .hypothesis (by simp [Δ])
    have hS : Context Δ S := Context.conjunctionLeft (Context.conjunctionRight hC)
    exact .mp hP (.mp hS (Context.under (Context.under hs C) P))
  have hv (v : Nat) (fresh : v ∉ assumptions.names) :
      ∀ q, q ∈ Γ → KDerivation (imp q (allCode v q)) := by
    intro q hq
    have he : q = H := by simpa [Γ] using hq
    subst q
    exact assumptions.vacuity v fresh
  have hall := Context.generalize 71 (hv 71 (by decide))
    (Context.generalize 59 (hv 59 (by decide))
      (Context.generalize 74 (hv 74 (by decide)) hp))
  apply Context.closeEmpty
  apply Context.deduction
  simpa [globalStep, allStepsCode, uniformStepCode, predecessorCore, P, Q, C] using hall

/-- Conditional represented match-graph collection on the entire source
domain: the source candidate and the actual inside-step K proof remain
explicit. This does not assert reverse totality, order preservation or PA
soundness. -/
def source_collection_of_inside (inside : InsideStep) : KDerivation
    (imp assumptions.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
      (existsCode 58 (replace 59 2 partialMatch).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let C := candidateCode 2 81 77 78 72 64 73 59 75
  let Γ := [C,assumptions.encode]
  have hc : Context Γ C := .head _ _
  have hh : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ globalStep := .mp hh (.closed (global_step_of_inside inside))
  exact .mp hs (.mp hc (.closed source_collection_of_step))

theorem source_collection_of_inside_certificate (inside : InsideStep) :
    theoremCode (certificate (source_collection_of_inside inside)) =
      imp assumptions.encode (imp (candidateCode 2 81 77 78 72 64 73 59 75)
        (existsCode 58 (replace 59 2 partialMatch).encode)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchCollectionInsideConditional

#print axioms PASoundness.PAtoCompactProductMatchCollectionInsideConditional.successor_of_inside
#print axioms PASoundness.PAtoCompactProductMatchCollectionInsideConditional.global_step_of_inside
#print axioms PASoundness.PAtoCompactProductMatchCollectionInsideConditional.source_collection_of_inside
#print axioms PASoundness.PAtoCompactProductMatchCollectionInsideConditional.source_collection_of_inside_certificate
