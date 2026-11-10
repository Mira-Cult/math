import PASoundness.PAtoCompactCandidateStepGeneralization
import PASoundness.PAtoCompactCandidateWitness
import PASoundness.PAtoCompactCandidateStepBinderTransport
import PASoundness.PAtoCompactFixedFirstRestrictedInduction
import PASoundness.PAtoCompactMultiplicationRowMapEdge

/-! Quantification of a supplied fixed-first row successor proof. The
map-bijection hypothesis is retained as a literal K antecedent, and the local
successor proof is an explicit proof-data input. This does not itself construct
a row graph, prove multiplication totality, or establish PA soundness. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstGuardedRestrictedStep
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateWitness
open PASoundness.PAtoCompactCandidateStepGeneralization PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactQuantifiedRefutation PASoundness.PAtoCompactCandidateStepBinderTransport
open PASoundness.PAtoCompactFixedFirstRestrictedInduction
open PASoundness.PAtoCompactMultiplicationRowMapEdge PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A local row-successor proof, expressed at the induction engine's names.
The fixed graph bijection remains an explicit antecedent. -/
def localCode : Nat := imp mapBijection.encode (imp (successorCode 204 205 208)
  (imp (replace 0 204 predicate).encode (replace 0 205 predicate).encode))

/-- Given the displayed local K proof, derive the exact candidate-restricted
step schema under the same fixed map-bijection assumption. -/
def exact_step_of_local (hlocal : KDerivation localCode) : KDerivation
    (imp mapBijection.encode (allCode 201
      (imp (candidateCode 201 213 209 210 202 0 203 205 206)
        (allStepsCode 201 0 204 205 208 209 210 predicate)))) := by
  let H := mapBijection.encode
  let C := candidateCode 201 213 209 210 202 0 203 231 206
  let Cy := candidateCode 204 230 209 210 232 0 203 231 206
  let Cz := candidateCode 205 234 209 210 237 0 240 231 206
  let P := predecessorCore 201 204 205 208 209 210
  let Fy := (replace 0 204 predicate).encode
  let Fz := (replace 0 205 predicate).encode
  have hvHy : KDerivation (imp H (allCode 204 H)) := mapBijection.vacuity 204 (by decide)
  have hvHz : KDerivation (imp H (allCode 205 H)) := mapBijection.vacuity 205 (by decide)
  have hvHY : KDerivation (imp H (allCode 201 H)) := mapBijection.vacuity 201 (by decide)
  have hvCy : KDerivation (imp C (allCode 204 C)) :=
    candidate_vacuity 201 213 209 210 202 0 203 231 206 204 (by decide)
  have hvCz : KDerivation (imp C (allCode 205 C)) :=
    candidate_vacuity 201 213 209 210 202 0 203 231 206 205 (by decide)
  have hp : KDerivation (imp H (imp Cy (imp Cz (imp P (imp Fy Fz))))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [Fy,P,Cz,Cy,H]
    have hf : Context Γ Fy := .head _ _
    have hP : Context Γ P := .hypothesis (by simp [Γ])
    have hh : Context Γ H := .hypothesis (by simp [Γ])
    have hs : Context Γ (successorCode 204 205 208) :=
      Context.conjunctionLeft (Context.conjunctionRight hP)
    exact .mp hf (.mp hs (.mp hh (.closed hlocal)))
  have hrestricted := candidate_restricted_step 201 204 205 208 213 209 210 230
    202 0 203 231 206 232 233 234 235 236 237 238 239 240 241 0 predicate H
    (by decide) (by decide) hvHy hvHz hvHY hvCy hvCz hp
  have halpha := restricted_step_witness_transport 201 213 209 210 202 0 203 205 206 231
    0 204 208 predicate (by decide) (by decide)
  exact compose hrestricted halpha

theorem exact_step_of_local_certificate (hlocal : KDerivation localCode) :
    theoremCode (certificate (exact_step_of_local hlocal)) =
      imp mapBijection.encode (allCode 201
        (imp (candidateCode 201 213 209 210 202 0 203 205 206)
          (allStepsCode 201 0 204 205 208 209 210 predicate))) :=
  certificate_correct (exact_step_of_local hlocal)
end PASoundness.PAtoCompactFixedFirstGuardedRestrictedStep
#print axioms PASoundness.PAtoCompactFixedFirstGuardedRestrictedStep.exact_step_of_local
#print axioms PASoundness.PAtoCompactFixedFirstGuardedRestrictedStep.exact_step_of_local_certificate
