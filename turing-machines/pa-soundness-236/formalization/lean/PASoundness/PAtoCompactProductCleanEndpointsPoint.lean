import PASoundness.PAtoCompactProductCleanFilter
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactProductCleanCoordinateAlias

/-! Extract the three endpoints of one queried nested product edge from the
explicit clean-member predicate for the same outer pair object. K pair
coordinate proofs are used; extensionality and unique pair representatives
are not assumed. This does not construct a clean graph, classify an
arbitrary old product witness, or prove multiplication totality. -/
namespace PASoundness.PAtoCompactProductCleanEndpointsPoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactProductCleanFilter PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactProductCleanCoordinateAlias
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The same outer edge 19 has the queried inner pair 18 and output 5. -/
def queryPairs : Formula := namedBoth (pairFormula 19 18 5) (pairFormula 18 3 4)
/-- The queried coordinates lie in the original three product domains. -/
def endpoints : Formula := namedBoth (.member 0 3)
  (namedBoth (.member 1 4) (.member 2 5))
private def body : Formula := namedBoth (.member 0 50) (namedBoth (.member 1 51)
  (namedBoth (.member 2 52) (namedBoth (pairFormula 53 50 51) (pairFormula 19 53 52))))

private def point : KDerivation (imp queryPairs.encode (imp body.encode endpoints.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [body.encode,queryPairs.encode]
  have hb : Context Γ body.encode := .head _ _
  have hq : Context Γ queryPairs.encode := .hypothesis (by simp [Γ])
  have hq' : Context Γ (both (pairFormula 19 18 5).encode (pairFormula 18 3 4).encode) := by
    simpa [queryPairs,namedBoth,Formula.not,Formula.encode,both,neg] using hq
  have hb' : Context Γ (both (member 0 50) (both (member 1 51)
      (both (member 2 52) (both (pairFormula 53 50 51).encode (pairFormula 19 53 52).encode)))) := by
    simpa [body,namedBoth,Formula.not,Formula.encode,both,neg] using hb
  have h1 := Context.conjunctionRight hb'
  have h2 := Context.conjunctionRight h1
  have h3 := Context.conjunctionRight h2
  have hcoords : Context Γ (both (both (equal 3 50) (equal 4 51)) (equal 5 52)) :=
    .mp (Context.conjunctionLeft h3) (.mp (Context.conjunctionRight hq')
      (.mp (Context.conjunctionRight h3) (.mp (Context.conjunctionLeft hq') (.closed clean_coordinates))))
  have ha : Context Γ (member 0 3) := .mp (Context.eqSymm (Context.conjunctionLeft (Context.conjunctionLeft hcoords)))
    (.mp (Context.conjunctionLeft hb') (.closed (memberRightEquality 0 50 3)))
  have hb2 : Context Γ (member 1 4) := .mp (Context.eqSymm (Context.conjunctionRight (Context.conjunctionLeft hcoords)))
    (.mp (Context.conjunctionLeft h1) (.closed (memberRightEquality 1 51 4)))
  have hc : Context Γ (member 2 5) := .mp (Context.eqSymm (Context.conjunctionRight hcoords))
    (.mp (Context.conjunctionLeft h2) (.closed (memberRightEquality 2 52 5)))
  simpa [endpoints,namedBoth,Formula.not,Formula.encode,both,neg] using
    Context.conjunctionIntro ha (Context.conjunctionIntro hb2 hc)

/-- A clean classification of the same outer edge forces its queried
coordinates into the three old product domains. -/
def endpoint_of_clean_member : KDerivation
    (imp queryPairs.encode (imp (cleanPredicate 19).encode endpoints.encode)) := by
  let B53 : Formula := namedBoth (pairFormula 53 50 51) (pairFormula 19 53 52)
  let A52 : Formula := namedBoth (.member 2 52) (.ex 53 B53)
  let A51 : Formula := namedBoth (.member 1 51) (.ex 52 A52)
  let A50 : Formula := namedBoth (.member 0 50) (.ex 51 A51)
  have c50 := endpoints.vacuity 50 (by decide)
  have c51 := endpoints.vacuity 51 (by decide)
  have c52 := endpoints.vacuity 52 (by decide)
  have c53 := endpoints.vacuity 53 (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(cleanPredicate 19).encode,queryPairs.encode]
  have he50 : Context Γ (existsCode 50 A50.encode) := by
    simpa [Γ,cleanPredicate,A50,A51,A52,B53,Formula.encode] using
      (Context.head [queryPairs.encode] (cleanPredicate 19).encode)
  apply Context.existsElim c50 _ he50
  apply Context.generalize 50
  · intro q hq
    change q ∈ [(cleanPredicate 19).encode,queryPairs.encode] at hq
    by_cases he : q = (cleanPredicate 19).encode
    · subst q; exact free_vacuity 50 (cleanPredicate 19) (by decide)
    · have he' : q = queryPairs.encode := by simpa [he] using hq
      subst q; exact queryPairs.vacuity 50 (by decide)
  apply Context.deduction
  let Δ := [A50.encode,(cleanPredicate 19).encode,queryPairs.encode]
  have ha50 : Context Δ A50.encode := .head _ _
  have ha50' : Context Δ (both (member 0 50) (existsCode 51 A51.encode)) := by
    simpa [A50,namedBoth,Formula.not,Formula.encode,both,neg] using ha50
  have he51 := Context.conjunctionRight ha50'
  apply Context.existsElim c51 _ he51
  apply Context.generalize 51
  · intro q hq
    change q ∈ [A50.encode,(cleanPredicate 19).encode,queryPairs.encode] at hq
    by_cases he : q = A50.encode
    · subst q; exact free_vacuity 51 A50 (by decide)
    · by_cases he' : q = (cleanPredicate 19).encode
      · subst q; exact free_vacuity 51 (cleanPredicate 19) (by decide)
      · have he'' : q = queryPairs.encode := by simpa [he,he'] using hq
        subst q; exact queryPairs.vacuity 51 (by decide)
  apply Context.deduction
  let Θ := [A51.encode,A50.encode,(cleanPredicate 19).encode,queryPairs.encode]
  have ha51 : Context Θ A51.encode := .head _ _
  have ha51' : Context Θ (both (member 1 51) (existsCode 52 A52.encode)) := by
    simpa [A51,namedBoth,Formula.not,Formula.encode,both,neg] using ha51
  have he52 := Context.conjunctionRight ha51'
  apply Context.existsElim c52 _ he52
  apply Context.generalize 52
  · intro q hq
    change q ∈ [A51.encode,A50.encode,(cleanPredicate 19).encode,queryPairs.encode] at hq
    by_cases he : q = A51.encode
    · subst q; exact free_vacuity 52 A51 (by decide)
    · by_cases he' : q = A50.encode
      · subst q; exact free_vacuity 52 A50 (by decide)
      · by_cases he'' : q = (cleanPredicate 19).encode
        · subst q; exact free_vacuity 52 (cleanPredicate 19) (by decide)
        · have he''' : q = queryPairs.encode := by simpa [he,he',he''] using hq
          subst q; exact queryPairs.vacuity 52 (by decide)
  apply Context.deduction
  let Ξ := [A52.encode,A51.encode,A50.encode,(cleanPredicate 19).encode,queryPairs.encode]
  have ha52 : Context Ξ A52.encode := .head _ _
  have ha52' : Context Ξ (both (member 2 52) (existsCode 53 B53.encode)) := by
    simpa [A52,namedBoth,Formula.not,Formula.encode,both,neg] using ha52
  have he53 := Context.conjunctionRight ha52'
  apply Context.existsElim c53 _ he53
  apply Context.generalize 53
  · intro q hq
    change q ∈ [A52.encode,A51.encode,A50.encode,(cleanPredicate 19).encode,queryPairs.encode] at hq
    by_cases he : q = A52.encode
    · subst q; exact free_vacuity 53 A52 (by decide)
    · by_cases he' : q = A51.encode
      · subst q; exact free_vacuity 53 A51 (by decide)
      · by_cases he'' : q = A50.encode
        · subst q; exact free_vacuity 53 A50 (by decide)
        · by_cases he''' : q = (cleanPredicate 19).encode
          · subst q; exact free_vacuity 53 (cleanPredicate 19) (by decide)
          · have he'''' : q = queryPairs.encode := by simpa [he,he',he'',he'''] using hq
            subst q; exact queryPairs.vacuity 53 (by decide)
  apply Context.deduction
  let Ω := [B53.encode,A52.encode,A51.encode,A50.encode,(cleanPredicate 19).encode,queryPairs.encode]
  have hp : Context Ω B53.encode := .head _ _
  have h0 : Context Ω A50.encode := .hypothesis (by simp [Ω])
  have h1 : Context Ω A51.encode := .hypothesis (by simp [Ω])
  have h2 : Context Ω A52.encode := .hypothesis (by simp [Ω])
  have hq : Context Ω queryPairs.encode := .hypothesis (by simp [Ω])
  have h0' : Context Ω (member 0 50) := Context.conjunctionLeft (by
    simpa [A50,namedBoth,Formula.not,Formula.encode,both,neg] using h0)
  have h1' : Context Ω (member 1 51) := Context.conjunctionLeft (by
    simpa [A51,namedBoth,Formula.not,Formula.encode,both,neg] using h1)
  have h2' : Context Ω (member 2 52) := Context.conjunctionLeft (by
    simpa [A52,namedBoth,Formula.not,Formula.encode,both,neg] using h2)
  have hb : Context Ω body.encode := by
    have hc := Context.conjunctionIntro h0' (Context.conjunctionIntro h1' (Context.conjunctionIntro h2' hp))
    simpa [body,B53,namedBoth,Formula.not,Formula.encode,both,neg] using hc
  exact .mp hb (.mp hq (.closed point))

theorem endpoint_of_clean_member_certificate : theoremCode (certificate endpoint_of_clean_member) =
    imp queryPairs.encode (imp (cleanPredicate 19).encode endpoints.encode) := certificate_correct _
end PASoundness.PAtoCompactProductCleanEndpointsPoint
#print axioms PASoundness.PAtoCompactProductCleanEndpointsPoint.endpoint_of_clean_member
#print axioms PASoundness.PAtoCompactProductCleanEndpointsPoint.endpoint_of_clean_member_certificate
