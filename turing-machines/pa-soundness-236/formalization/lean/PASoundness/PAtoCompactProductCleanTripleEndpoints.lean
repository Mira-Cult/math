import PASoundness.PAtoCompactProductCleanEndpointsPoint
import PASoundness.PAtoCompactOldTripleEdgeExtract

/-! Endpoint extraction for an old product triple under the explicit clean
old-graph hypothesis. The clean graph and triple use the same outer witness;
no extensionality, raw-product cleanliness, or multiplication totality is
assumed. -/
namespace PASoundness.PAtoCompactProductCleanTripleEndpoints
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactProductCleanFilter PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactProductCleanEndpointsPoint PASoundness.PAtoCompactOldTripleEdgeExtract
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The supplied graph 10 contains only nested triples with endpoints in
old domains 0, 1, 2. -/
def oldClean : Formula := .all 19 (.imp (.member 10 19) (cleanPredicate 19))

private def point : KDerivation (imp oldClean.encode
    (imp (namedBoth coords outerBody).encode endpoints.encode)) := by
  let cb : Formula := .imp (.member 10 19) (cleanPredicate 19)
  have hi := allSpecialize 19 cb (by decide)
  have hi' : KDerivation (imp oldClean.encode (imp (member 10 19) (cleanPredicate 19).encode)) := by
    simpa [oldClean,cb,Formula.encode] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(namedBoth coords outerBody).encode,oldClean.encode]
  have he : Context Γ (both coords.encode (both (member 10 19) (pairFormula 19 18 5).encode)) := by
    have h : Context Γ (namedBoth coords outerBody).encode := .head _ _
    simpa [outerBody,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ (cleanPredicate 19).encode :=
    .mp (Context.conjunctionLeft (Context.conjunctionRight he)) (.mp hc (.closed hi'))
  have hq : Context Γ queryPairs.encode := by
    have h := Context.conjunctionIntro (Context.conjunctionRight (Context.conjunctionRight he))
      (Context.conjunctionLeft he)
    simpa [queryPairs,coords,namedBoth,Formula.not,Formula.encode,both,neg] using h
  exact .mp hp (.mp hq (.closed endpoint_of_clean_member))

private def lift_exists (x P A B : Nat)
    (hP : KDerivation (imp P (allCode x P))) (hB : KDerivation (imp B (allCode x B)))
    (h : KDerivation (imp P (imp A B))) : KDerivation (imp P (imp (existsCode x A) B)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have hp : Context [P] P := .head _ _
  have hpstep : Context [P] (imp A B) := .mp hp (.closed h)
  have hv : ∀ z, z ∈ [P] → KDerivation (imp z (allCode x z)) := by
    intro z hz
    have he : z = P := by simpa using hz
    subst z
    exact hP
  have hall : Context [P] (allCode x (imp A B)) := Context.generalize x hv hpstep
  exact Context.existsElim hB (.under hall _) (.head _ _)

/-- An actual triple in the explicitly clean old graph has all three
required old-domain endpoint memberships. -/
def triple_endpoints : KDerivation (imp oldClean.encode (imp oldTriple.encode endpoints.encode)) := by
  have hc19 := free_vacuity 19 oldClean (by decide)
  have hc18 := oldClean.vacuity 18 (by decide)
  have he19 := endpoints.vacuity 19 (by decide)
  have he18 := endpoints.vacuity 18 (by decide)
  have h19 := lift_exists 19 oldClean.encode (namedBoth coords outerBody).encode endpoints.encode hc19 he19 point
  have h18 := lift_exists 18 oldClean.encode (existsCode 19 (namedBoth coords outerBody).encode) endpoints.encode hc18 he18 h19
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldTriple.encode,oldClean.encode]
  have ht : Context Γ oldTriple.encode := .head _ _
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  have he := Context.mp ht (.closed triple_to_expanded)
  change Context Γ (existsCode 18 (existsCode 19 (namedBoth coords outerBody).encode)) at he
  exact .mp he (.mp hc (.closed h18))

theorem triple_endpoints_certificate : theoremCode (certificate triple_endpoints) =
    imp oldClean.encode (imp oldTriple.encode endpoints.encode) := certificate_correct _
end PASoundness.PAtoCompactProductCleanTripleEndpoints
#print axioms PASoundness.PAtoCompactProductCleanTripleEndpoints.triple_endpoints
#print axioms PASoundness.PAtoCompactProductCleanTripleEndpoints.triple_endpoints_certificate
