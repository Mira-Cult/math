import PASoundness.PAtoCompactProductOutputOutsideStep
import PASoundness.PAtoCompactProductOutputInductionFixture

/-! Candidate-prefix collection for the transported product graph, conditional
on the inside-source successor construction. The latter remains explicit K
proof data; this module does not construct it or prove output transport. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputCollectionInsideConditional

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactUniformStep PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactQuantifiedRefutation PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductOutputImagePoint PASoundness.PAtoCompactProductOutputPartialBase
open PASoundness.PAtoCompactProductOutputOutsidePath PASoundness.PAtoCompactProductOutputOutsideStep
open PASoundness.PAtoCompactProductOutputInductionFixture

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Source product on factors 43 and 44 with outputs in 0, together with the
output isomorphism from 0 to 42. -/
def assumptions : Formula := namedBoth
  (replace 81 44 (replace 80 43 sourceMatrix)) firstBijection

/-- The still-unproved inside-source extension, retaining the actual source
matrix and output bijection as object-level hypotheses. -/
def InsideStep : Type := KDerivation (imp assumptions.encode
  (imp (successorCode 74 59 76) (imp (member 0 74)
    (imp (replace 64 74 predicate).encode (replace 64 59 predicate).encode))))

/-- Combine the explicit inside proof with the proved outside branch. -/
def successor_of_inside (inside : InsideStep) : KDerivation
    (imp assumptions.encode (imp (successorCode 74 59 76)
      (imp (replace 64 74 predicate).encode (replace 64 59 predicate).encode))) := by
  let H := assumptions.encode
  let S := successorCode 74 59 76
  let X := member 0 74
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
    have hg : Context Δ PAtoCompactProductOutputOutsidePath.guard.encode := by
      have h := Context.conjunctionIntro hs' hn
      simpa [PAtoCompactProductOutputOutsidePath.guard, namedSuccessor, namedSuccessorBody, successorCode, namedBoth, namedEither,
        CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, either, S, X] using h
    exact .mp hp' (.mp hg (.closed outside_predicate_step))

/-- The candidate-induction global step, still conditional on InsideStep. -/
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

/-- A graph over the candidate prefix, conditional on the source matrix,
output bijection, candidate prefix and the inside successor K proof. -/
def prefix_collection_of_inside (inside : InsideStep) : KDerivation
    (imp assumptions.encode (imp candidatePrefix
      (existsCode 58 (replace 59 70 partialInvariant).encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [candidatePrefix, assumptions.encode]
  have hc : Context Γ candidatePrefix := .head _ _
  have hh : Context Γ assumptions.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ globalStep := .mp hh (.closed (global_step_of_inside inside))
  exact .mp hs (.mp hc (.closed prefix_collection_of_step))

theorem prefix_collection_of_inside_certificate (inside : InsideStep) :
    theoremCode (certificate (prefix_collection_of_inside inside)) =
      imp assumptions.encode (imp candidatePrefix
        (existsCode 58 (replace 59 70 partialInvariant).encode)) := certificate_correct _

end PASoundness.PAtoCompactProductOutputCollectionInsideConditional

#print axioms PASoundness.PAtoCompactProductOutputCollectionInsideConditional.successor_of_inside
#print axioms PASoundness.PAtoCompactProductOutputCollectionInsideConditional.global_step_of_inside
#print axioms PASoundness.PAtoCompactProductOutputCollectionInsideConditional.prefix_collection_of_inside
#print axioms PASoundness.PAtoCompactProductOutputCollectionInsideConditional.prefix_collection_of_inside_certificate
