import PASoundness.PAtoCompactFixedFirstRowWitnessAlpha
import PASoundness.PAtoCompactMultiplicationRowCoordinateAlias

/-! K elimination of the explicit new-row witness for one queried product
edge. Equality follows from two pair descriptions of the same outer object;
no extensionality or uniqueness of pair representatives is assumed. The
new-row branch itself is an explicit premise: no graph case split, complete
row construction, lexicographic theorem, or multiplication totality is
asserted. -/
namespace PASoundness.PAtoCompactMultiplicationRowQueryFirst
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactFixedFirstRowWitnessAlpha PASoundness.PAtoCompactMultiplicationRowCoordinateAlias
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def queryPairs : Formula := namedBoth (pairFormula 63 18 5) (pairFormula 18 3 4)
def queryResult : Formula := namedBoth (.equal 3 30)
  (namedBoth (.member 31 4) (graphFormula 6 4 5))

/-- From two descriptions of the same outer edge and a freshened row body,
extract the queried major equality and its corresponding suffix-map edge. -/
private def point : KDerivation (imp queryPairs.encode (imp body3.encode queryResult.encode)) := by
  have h1 := (equalityReplace 60 4 (graphFormula 6 60 61) (by decide) (by decide)).1
  have hr1 : replace 60 4 (graphFormula 6 60 61) = graphFormula 6 4 61 := by decide
  rw [hr1] at h1
  have h2 := (equalityReplace 61 5 (graphFormula 6 4 61) (by decide) (by decide)).1
  have hr2 : replace 61 5 (graphFormula 6 4 61) = graphFormula 6 4 5 := by decide
  rw [hr2] at h2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [body3.encode,queryPairs.encode]
  have hb : Context Γ body3.encode := .head _ _
  have hq : Context Γ queryPairs.encode := .hypothesis (by simp [Γ])
  have hq' : Context Γ (both (pairFormula 63 18 5).encode (pairFormula 18 3 4).encode) := by
    simpa [queryPairs,namedBoth,Formula.not,Formula.encode,both,neg] using hq
  have hb' : Context Γ (both (member 0 60) (both (member 31 60)
      (both (graphFormula 6 60 61).encode
        (both (pairFormula 62 30 60).encode (pairFormula 63 62 61).encode)))) := by
    simpa [fresh_body_shape,namedBoth,Formula.not,Formula.encode,both,neg] using hb
  have hright := Context.conjunctionRight hb'
  have hm : Context Γ (member 31 60) := Context.conjunctionLeft hright
  have hedge : Context Γ (graphFormula 6 60 61).encode := Context.conjunctionLeft (Context.conjunctionRight hright)
  have hpairs := Context.conjunctionRight (Context.conjunctionRight hright)
  have hcoords : Context Γ (both (both (equal 3 30) (equal 4 60)) (equal 5 61)) :=
    .mp (Context.conjunctionLeft hpairs) (.mp (Context.conjunctionRight hq')
      (.mp (Context.conjunctionRight hpairs) (.mp (Context.conjunctionLeft hq') (.closed row_coordinates))))
  have hmajor : Context Γ (equal 3 30) := Context.conjunctionLeft (Context.conjunctionLeft hcoords)
  have hminor : Context Γ (equal 60 4) := Context.eqSymm (Context.conjunctionRight (Context.conjunctionLeft hcoords))
  have hout : Context Γ (equal 61 5) := Context.eqSymm (Context.conjunctionRight hcoords)
  have hmem : Context Γ (member 31 4) := .mp hminor (.mp hm (.closed (memberRightEquality 31 60 4)))
  have hedge1 : Context Γ (graphFormula 6 4 61).encode := .mp hedge (.mp hminor (.closed h1))
  have hedge2 : Context Γ (graphFormula 6 4 5).encode := .mp hedge1 (.mp hout (.closed h2))
  have hc := Context.conjunctionIntro hmajor (Context.conjunctionIntro hmem hedge2)
  simpa [queryResult,namedBoth,Formula.not,Formula.encode,both,neg] using hc

private def lift_exists (x P A B : Nat)
    (hP : KDerivation (imp P (allCode x P)))
    (hB : KDerivation (imp B (allCode x B)))
    (h : KDerivation (imp P (imp A B))) : KDerivation (imp P (imp (existsCode x A) B)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [existsCode x A,P]
  have hp : Context [P] P := .head _ _
  have hpstep : Context [P] (imp A B) := .mp hp (.closed h)
  have hv : ∀ z, z ∈ [P] → KDerivation (imp z (allCode x z)) := by
    intro z hz
    have he : z = P := by simpa using hz
    subst z
    exact hP
  have hall : Context [P] (allCode x (imp A B)) := Context.generalize x hv hpstep
  exact Context.existsElim hB (.under hall _) (.head _ _)

/-- The actual alpha-fresh new-row branch, together with the two explicit
queried pair descriptions, yields major equality, minor-domain membership,
and the supplied suffix-map edge at the queried labels. -/
def row_query : KDerivation (imp queryPairs.encode
    (imp (replace 9 63 rowWitness).encode queryResult.encode)) := by
  have p60 := queryPairs.vacuity 60 (by decide)
  have p61 := queryPairs.vacuity 61 (by decide)
  have p62 := queryPairs.vacuity 62 (by decide)
  have c60 := queryResult.vacuity 60 (by decide)
  have c61 := queryResult.vacuity 61 (by decide)
  have c62 := queryResult.vacuity 62 (by decide)
  have h62 := lift_exists 62 queryPairs.encode body3.encode queryResult.encode p62 c62 point
  have h61 := lift_exists 61 queryPairs.encode (existsCode 62 body3.encode) queryResult.encode p61 c61 h62
  have h60 := lift_exists 60 queryPairs.encode (existsCode 61 (existsCode 62 body3.encode)) queryResult.encode p60 c60 h61
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(replace 9 63 rowWitness).encode,queryPairs.encode]
  have hr : Context Γ (replace 9 63 rowWitness).encode := .head _ _
  have hq : Context Γ queryPairs.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ freshRowWitness.encode := .mp hr (.closed row_witness_alpha.1)
  change Context Γ (existsCode 60 (existsCode 61 (existsCode 62 body3.encode))) at hf
  exact .mp hf (.mp hq (.closed h60))

theorem row_query_certificate : theoremCode (certificate row_query) =
    imp queryPairs.encode (imp (replace 9 63 rowWitness).encode queryResult.encode) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationRowQueryFirst
#print axioms PASoundness.PAtoCompactMultiplicationRowQueryFirst.row_query
#print axioms PASoundness.PAtoCompactMultiplicationRowQueryFirst.row_query_certificate
