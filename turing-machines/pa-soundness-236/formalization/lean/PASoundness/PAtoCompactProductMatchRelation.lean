import PASoundness.PAtoCompactProductMatchPathUnique
import PASoundness.PAtoCompactExistsCommute
import PASoundness.PAtoCompactSuccGraphOutputLift

/-! The concrete local product-match relation, with K proofs of a target
value and uniqueness from the displayed product and factor-bijection
matrices. This does not collect the relation into a represented graph,
establish its reverse totality/order clause, or prove product congruence. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchRelation

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductMatchPointWitness PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductMatchTargetOutput PASoundness.PAtoCompactProductMatchTargetWitness
open PASoundness.PAtoCompactProductMatchSourceWitness PASoundness.PAtoCompactProductMatchPathUnique
open PASoundness.PAtoCompactExistsCommute PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactMulTermTransportWitness

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Source output 32 and target output 35 are the free output names. -/
def path : Formula := .ex 30 (.ex 31 (.ex 33 (.ex 34 retainedMatchBody)))

/-- The same relation with target name 55, using fresh local witness names. -/
def rivalPath : Formula := .ex 50 (.ex 51 (.ex 53 (.ex 54 rivalMatchBody)))

/-- Freshly rename the four private source and factor-image witnesses.
This is a proof-data equivalence, not identification of represented values. -/
def rival_alpha : ProofEquiv (replace 35 55 path) rivalPath := by
  let R := replace 35 55 retainedMatchBody
  let W := replace 31 51 (replace 30 50 R)
  have hstart : replace 35 55 path = .ex 30 (.ex 31 (.ex 33 (.ex 34 R))) := by decide
  have h1 := two_exists_alpha (.ex 33 (.ex 34 R)) 30 31 50 51
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hmid : replace 31 51 (replace 30 50 (.ex 33 (.ex 34 R))) =
      .ex 33 (.ex 34 W) := by decide
  rw [hmid] at h1
  have h2 := two_exists_alpha W 33 34 53 54
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hend : replace 34 54 (replace 33 53 W) = rivalMatchBody := by decide
  rw [hend] at h2
  rw [hstart]
  exact h1.trans (ProofEquiv.existential 50 (ProofEquiv.existential 51 h2))

/-- Move the selected target output outside the four auxiliary witnesses. -/
def path_exists : KDerivation
    (imp productMatrix.encode (imp (member 2 32)
      (imp firstBijection.encode (imp secondBijection.encode (imp targetMatrix.encode
        (existsCode 35 path.encode)))))) := by
  let R := retainedMatchBody.encode
  have h1 := existsCongr 30 (existsCongr 31 (existsCongr 33 (exists_commute 34 35 R)))
  have h2 := existsCongr 30 (existsCongr 31 (exists_commute 33 35 (existsCode 34 R)))
  have h3 := existsCongr 30 (exists_commute 31 35 (existsCode 33 (existsCode 34 R)))
  have h4 := exists_commute 30 35 (existsCode 31 (existsCode 33 (existsCode 34 R)))
  have hswap := compose h1 (compose h2 (compose h3 h4))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [targetMatrix.encode,secondBijection.encode,firstBijection.encode,member 2 32,productMatrix.encode]
  have ht : Context Γ targetMatrix.encode := .head _ _
  have hb₂ : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hb₁ : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have ho : Context Γ (member 2 32) := .hypothesis (by simp [Γ])
  have hp : Context Γ productMatrix.encode := .hypothesis (by simp [Γ])
  have hw := Context.mp ht (Context.mp hb₂ (Context.mp hb₁
    (Context.mp ho (Context.mp hp (.closed matched_path_exists)))))
  simpa [path, Formula.encode, R] using Context.mp hw (.closed hswap)

/-- Two related target values for the same source value are equal. The
relational paths and all source/target graph clauses are literal antecedents. -/
def path_functional : KDerivation
    (imp path.encode (imp (replace 35 55 path).encode (equal 55 35))) := by
  let E : Formula := .equal 55 35
  have hr54 := guarded_exists_left 54 retainedMatchBody.encode rivalMatchBody.encode E.encode
    (retainedMatchBody.vacuity 54 (by decide)) (E.vacuity 54 (by decide)) matched_output_unique
  have hr53 := guarded_exists_left 53 retainedMatchBody.encode
    (existsCode 54 rivalMatchBody.encode) E.encode
    (retainedMatchBody.vacuity 53 (by decide)) (E.vacuity 53 (by decide)) hr54
  have hr51 := guarded_exists_left 51 retainedMatchBody.encode
    (existsCode 53 (existsCode 54 rivalMatchBody.encode)) E.encode
    (retainedMatchBody.vacuity 51 (by decide)) (E.vacuity 51 (by decide)) hr53
  have hr50 := guarded_exists_left 50 retainedMatchBody.encode
    (existsCode 51 (existsCode 53 (existsCode 54 rivalMatchBody.encode))) E.encode
    (retainedMatchBody.vacuity 50 (by decide)) (E.vacuity 50 (by decide)) hr51
  have hflip : KDerivation (imp rivalPath.encode (imp retainedMatchBody.encode E.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [retainedMatchBody.encode,rivalPath.encode]
    have hr : Context Γ retainedMatchBody.encode := .head _ _
    have hp : Context Γ rivalPath.encode := .hypothesis (by simp [Γ])
    have h := Context.mp hp (Context.mp hr (.closed hr50))
    simpa [Γ, rivalPath, Formula.encode] using h
  have hs34 := guarded_exists_left 34 rivalPath.encode retainedMatchBody.encode E.encode
    (rivalPath.vacuity 34 (by decide)) (E.vacuity 34 (by decide)) hflip
  have hs33 := guarded_exists_left 33 rivalPath.encode
    (existsCode 34 retainedMatchBody.encode) E.encode
    (rivalPath.vacuity 33 (by decide)) (E.vacuity 33 (by decide)) hs34
  have hs31 := guarded_exists_left 31 rivalPath.encode
    (existsCode 33 (existsCode 34 retainedMatchBody.encode)) E.encode
    (rivalPath.vacuity 31 (by decide)) (E.vacuity 31 (by decide)) hs33
  have hs30 := guarded_exists_left 30 rivalPath.encode
    (existsCode 31 (existsCode 33 (existsCode 34 retainedMatchBody.encode))) E.encode
    (rivalPath.vacuity 30 (by decide)) (E.vacuity 30 (by decide)) hs31
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(replace 35 55 path).encode,path.encode]
  have hp' : Context Γ (replace 35 55 path).encode := .head _ _
  have hp : Context Γ path.encode := .hypothesis (by simp [Γ])
  have hrival : Context Γ rivalPath.encode := .mp hp' (.closed rival_alpha.forward)
  have h := Context.mp hp (Context.mp hrival (.closed hs30))
  simpa [Γ, path, E, Formula.encode] using h

theorem path_exists_certificate : theoremCode (certificate path_exists) =
    imp productMatrix.encode (imp (member 2 32)
      (imp firstBijection.encode (imp secondBijection.encode (imp targetMatrix.encode
        (existsCode 35 path.encode))))) := certificate_correct _

theorem path_functional_certificate : theoremCode (certificate path_functional) =
    imp path.encode (imp (replace 35 55 path).encode (equal 55 35)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchRelation

#print axioms PASoundness.PAtoCompactProductMatchRelation.rival_alpha
#print axioms PASoundness.PAtoCompactProductMatchRelation.path_exists
#print axioms PASoundness.PAtoCompactProductMatchRelation.path_functional
#print axioms PASoundness.PAtoCompactProductMatchRelation.path_exists_certificate
#print axioms PASoundness.PAtoCompactProductMatchRelation.path_functional_certificate
