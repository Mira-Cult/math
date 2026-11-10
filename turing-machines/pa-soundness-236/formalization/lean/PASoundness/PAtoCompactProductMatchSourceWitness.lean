import PASoundness.PAtoCompactProductMatchTargetWitness

/-! Existence of one full source-to-target product match, retaining the source
reverse witness, both factor-isomorphism image witnesses and target product
output. This is a pointwise finite-K construction. It does not collect a
represented match graph or prove global product functionality/congruence. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchSourceWitness

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductMatchPointWitness PASoundness.PAtoCompactProductMatchFactorImages
open PASoundness.PAtoCompactProductMatchTargetOutput PASoundness.PAtoCompactProductMatchTargetWitness

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def retainedMatchBody : Formula := namedBoth selectedReverseBody matchBody
def guard : Formula := namedBoth firstBijection (namedBoth secondBijection targetMatrix)

/-- Retain the selected source witness inside the three target-side
existentials, rather than discarding the source product triple. -/
def retained_target_exists : KDerivation
    (imp selectedReverseBody.encode (imp firstBijection.encode (imp secondBijection.encode
      (imp targetMatrix.encode (existsCode 33 (existsCode 34 (existsCode 35 retainedMatchBody.encode))))))) := by
  let R := selectedReverseBody.encode
  let P := matchBody.encode
  let Q := retainedMatchBody.encode
  have hlocal : KDerivation (imp R (imp P Q)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [P,R]
    have hp : Context Γ P := .head _ _
    have hr : Context Γ R := .hypothesis (by simp [Γ])
    have h := Context.conjunctionIntro hr hp
    simpa [Q, R, P, retainedMatchBody, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have h35 := conditionalExistsCongr 35 (selectedReverseBody.vacuity 35 (by decide)) hlocal
  have h34 := conditionalExistsCongr 34 (selectedReverseBody.vacuity 34 (by decide)) h35
  have h33 := conditionalExistsCongr 33 (selectedReverseBody.vacuity 33 (by decide)) h34
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [targetMatrix.encode,secondBijection.encode,firstBijection.encode,R]
  have hm : Context Γ targetMatrix.encode := .head _ _
  have hb₂ : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hb₁ : Context Γ firstBijection.encode := .hypothesis (by simp [Γ])
  have hr : Context Γ R := .hypothesis (by simp [Γ])
  have hex := Context.mp hm (Context.mp hb₂ (Context.mp hb₁ (Context.mp hr (.closed matched_target_exists))))
  exact .mp hex (.mp hr (.closed h33))

/-- Any source-output member has one matched target-output witness through
the two supplied factor bijection matrices and target product matrix. All
five witnesses and their underlying edge and uniqueness clauses are retained. -/
def matched_path_exists : KDerivation
    (imp productMatrix.encode (imp (member 2 32)
      (imp firstBijection.encode (imp secondBijection.encode (imp targetMatrix.encode
        (existsCode 30 (existsCode 31 (existsCode 33 (existsCode 34
          (existsCode 35 retainedMatchBody.encode)))))))))) := by
  let R := selectedReverseBody.encode
  let G := guard.encode
  let Q := existsCode 33 (existsCode 34 (existsCode 35 retainedMatchBody.encode))
  have hpoint : KDerivation (imp G (imp R Q)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [R,G]
    have hr : Context Γ R := .head _ _
    have hg : Context Γ G := .hypothesis (by simp [Γ])
    have hg' : Context Γ (both firstBijection.encode
        (both secondBijection.encode targetMatrix.encode)) := by
      simpa [G, guard, namedBoth, Formula.not, Formula.encode, both, neg] using hg
    have hb₁ := Context.conjunctionLeft hg'
    have hb₂ := Context.conjunctionLeft (Context.conjunctionRight hg')
    have hm := Context.conjunctionRight (Context.conjunctionRight hg')
    exact .mp hm (.mp hb₂ (.mp hb₁ (.mp hr (.closed retained_target_exists))))
  have h31 := conditionalExistsCongr 31 (guard.vacuity 31 (by decide)) hpoint
  have h30 := conditionalExistsCongr 30 (guard.vacuity 30 (by decide)) h31
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
  have hr : Context Γ (existsCode 30 (existsCode 31 R)) :=
    .mp ho (.mp hp (.closed reverse_coordinates))
  have hg : Context Γ G := by
    have h := Context.conjunctionIntro hb₁ (Context.conjunctionIntro hb₂ ht)
    simpa [G, guard, namedBoth, Formula.not, Formula.encode, both, neg] using h
  exact .mp hr (.mp hg (.closed h30))

theorem matched_path_exists_certificate : theoremCode (certificate matched_path_exists) =
    imp productMatrix.encode (imp (member 2 32)
      (imp firstBijection.encode (imp secondBijection.encode (imp targetMatrix.encode
        (existsCode 30 (existsCode 31 (existsCode 33 (existsCode 34
          (existsCode 35 retainedMatchBody.encode))))))))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchSourceWitness

#print axioms PASoundness.PAtoCompactProductMatchSourceWitness.retained_target_exists
#print axioms PASoundness.PAtoCompactProductMatchSourceWitness.matched_path_exists
#print axioms PASoundness.PAtoCompactProductMatchSourceWitness.matched_path_exists_certificate
