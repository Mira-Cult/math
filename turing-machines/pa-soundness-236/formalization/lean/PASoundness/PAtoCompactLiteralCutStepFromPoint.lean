import PASoundness.PAtoCompactCandidateStepGeneralization
import PASoundness.PAtoCompactCandidateWitness
import PASoundness.PAtoCompactLiteralCutRestrictedInduction
import PASoundness.PAtoCompactCandidateStepBinderTransport

/-! A fixed-name candidate-restricted global step constructor for the
literal-cut predicate. The pointwise preservation derivation is an
explicit input. The candidate container uses fresh binder 231, rather than
205, because 205 is the step's free successor name before generalization.
No addition totality or PA induction is claimed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutStepFromPoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateWitness
open PASoundness.PAtoCompactCandidateStepGeneralization PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactQuantifiedRefutation PASoundness.PAtoCompactLiteralCutAdditionDefinition
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def trivial : Formula := .imp (.member 30 30) (.member 30 30)
/-- The explicit local candidate-endpoint preservation obligation. -/
def pointCode : Nat :=
  imp (candidateCode 204 230 209 210 232 31 203 231 206)
    (imp (candidateCode 205 234 209 210 237 31 240 231 206)
      (imp (predecessorCore 201 204 205 208 209 210)
        (imp (replace 31 204 predicate).encode (replace 31 205 predicate).encode)))

/-- From a finite pointwise K derivation with the displayed candidate and
predecessor hypotheses, build the quantified candidate-restricted step.
The pointwise step remains an explicit proof-data input. -/
def restricted_step_of_point (hpoint : KDerivation pointCode) : KDerivation
    (allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 231 206)
      (allStepsCode 201 31 204 205 208 209 210 predicate))) := by
  let H := trivial.encode
  have hh : KDerivation H := by
    exact PASoundness.CompactHilbertBasis.identity (member 30 30)
  have hvHy : KDerivation (imp H (allCode 204 H)) := trivial.vacuity 204 (by decide)
  have hvHz : KDerivation (imp H (allCode 205 H)) := trivial.vacuity 205 (by decide)
  have hvHY : KDerivation (imp H (allCode 201 H)) := trivial.vacuity 201 (by decide)
  have hvCy : KDerivation (imp (candidateCode 201 213 209 210 202 31 203 231 206)
      (allCode 204 (candidateCode 201 213 209 210 202 31 203 231 206))) :=
    candidate_vacuity 201 213 209 210 202 31 203 231 206 204 (by decide)
  have hvCz : KDerivation (imp (candidateCode 201 213 209 210 202 31 203 231 206)
      (allCode 205 (candidateCode 201 213 209 210 202 31 203 231 206))) :=
    candidate_vacuity 201 213 209 210 202 31 203 231 206 205 (by decide)
  have hp : KDerivation (imp H pointCode) := Context.closeEmpty (Context.deduction (.closed hpoint))
  exact .mp hh (candidate_restricted_step 201 204 205 208 213 209 210 230
    202 31 203 231 206 232 233 234 235 236 237 238 239 240 241 31 predicate H
    (by decide) (by decide) hvHy hvHz hvHY hvCy hvCz hp)

theorem restricted_step_of_point_certificate (hpoint : KDerivation pointCode) :
    theoremCode (certificate (restricted_step_of_point hpoint)) =
      allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 231 206)
        (allStepsCode 201 31 204 205 208 209 210 predicate)) :=
  certificate_correct (restricted_step_of_point hpoint)


/-- The quantified schema at the exact binder used by the literal-cut
induction theorem, from the explicitly supplied local point proof. -/
def exact_step_of_point (hpoint : KDerivation pointCode) : KDerivation
    (allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 205 206)
      (allStepsCode 201 31 204 205 208 209 210 predicate))) := by
  exact .mp (restricted_step_of_point hpoint)
    (PASoundness.PAtoCompactCandidateStepBinderTransport.restricted_step_witness_transport
      201 213 209 210 202 31 203 205 206 231 31 204 208 predicate (by decide) (by decide))

theorem exact_step_of_point_certificate (hpoint : KDerivation pointCode) :
    theoremCode (certificate (exact_step_of_point hpoint)) =
      allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 205 206)
        (allStepsCode 201 31 204 205 208 209 210 predicate)) :=
  certificate_correct (exact_step_of_point hpoint)

/-- The induction conclusion follows from a supplied point step and the
explicit uniform zero-base proof. Neither premise is asserted here. -/
def induction_from_point_and_base
    (hpoint : KDerivation pointCode)
    (hbase : KDerivation (PASoundness.PAtoCompactUniformBase.uniformBaseCode 31 205 207 predicate)) :
    KDerivation (imp (candidateCode 200 213 209 210 202 31 203 205 206)
      (replace 31 200 predicate).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let D := candidateCode 200 213 209 210 202 31 203 205 206
  have hd : Context [D] D := .head _ _
  exact .mp (.closed (exact_step_of_point hpoint))
    (.mp (.closed hbase) (.mp hd (.closed PASoundness.PAtoCompactLiteralCutRestrictedInduction.fixed_induction)))

theorem induction_from_point_and_base_certificate
    (hpoint : KDerivation pointCode)
    (hbase : KDerivation (PASoundness.PAtoCompactUniformBase.uniformBaseCode 31 205 207 predicate)) :
    theoremCode (certificate (induction_from_point_and_base hpoint hbase)) =
      imp (candidateCode 200 213 209 210 202 31 203 205 206)
        (replace 31 200 predicate).encode :=
  certificate_correct (induction_from_point_and_base hpoint hbase)

end PASoundness.PAtoCompactLiteralCutStepFromPoint
#print axioms PASoundness.PAtoCompactLiteralCutStepFromPoint.restricted_step_of_point
#print axioms PASoundness.PAtoCompactLiteralCutStepFromPoint.restricted_step_of_point_certificate

#print axioms PASoundness.PAtoCompactLiteralCutStepFromPoint.exact_step_of_point
#print axioms PASoundness.PAtoCompactLiteralCutStepFromPoint.induction_from_point_and_base
#print axioms PASoundness.PAtoCompactLiteralCutStepFromPoint.induction_from_point_and_base_certificate
#print axioms PASoundness.PAtoCompactLiteralCutStepFromPoint.exact_step_of_point_certificate
