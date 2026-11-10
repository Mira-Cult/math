import PASoundness.PAtoCompactProductOldSuffixExclusion
import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.PAtoCompactFreeVacuity

/-! Endpoint extraction for a queried old product triple at competitor
coordinates (7,8,5). The clean old graph is explicit. Equality of coordinates
comes from two pair descriptions of the same edge, not uniqueness of pair
representatives or extensionality. This does not prove a product matrix,
graph extension, multiplication totality, or PA soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOldCompetitorEndpoints
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactProductCleanFilter
open PASoundness.PAtoCompactProductCleanEndpointsPoint PASoundness.PAtoCompactProductOldSuffixExclusion
open PASoundness.PAtoCompactFreeVacuity
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The queried competitor triple in old graph 10. -/
def oldCompetitor : Formula := replace 6 10 (tripleFormula 7 8 5)
/-- The competitor's three desired old-domain memberships. -/
def competitorEndpoints : Formula := namedBoth (.member 30 7)
  (namedBoth (.member 31 8) (.member 32 5))
private def query78 : Formula := replace 4 8 (replace 3 7 queryPairs)
private def clean19 : Formula := replace 2 32 (replace 1 31 (replace 0 30 (cleanPredicate 19)))
private def source : Formula := .imp queryPairs (.imp (cleanPredicate 19) endpoints)
private def f30 : Formula := replace 0 30 source
private def f31 : Formula := replace 1 31 f30
private def f32 : Formula := replace 2 32 f31
private def f7 : Formula := replace 3 7 f32
private def f8 : Formula := replace 4 8 f7

private def relabel_point : KDerivation f8.encode := by
  have h0 : KDerivation source.encode := endpoint_of_clean_member
  have h1 : KDerivation f30.encode := .mp (.generalize 0 h0)
    (universalInstance 0 30 source (by decide) (by decide) (by decide))
  have h2 : KDerivation f31.encode := .mp (.generalize 1 h1)
    (universalInstance 1 31 f30 (by decide) (by decide) (by decide))
  have h3 : KDerivation f32.encode := .mp (.generalize 2 h2)
    (universalInstance 2 32 f31 (by decide) (by decide) (by decide))
  have h4 : KDerivation f7.encode := .mp (.generalize 3 h3)
    (universalInstance 3 7 f32 (by decide) (by decide) (by decide))
  exact .mp (.generalize 4 h4) (universalInstance 4 8 f7 (by decide) (by decide) (by decide))

private def point : KDerivation (imp oldClean.encode (imp (member 10 19)
    (imp query78.encode competitorEndpoints.encode))) := by
  let F : Formula := .imp (.member 10 19) clean19
  have hi := allSpecialize 19 F (by decide)
  have hp : KDerivation (imp query78.encode (imp clean19.encode competitorEndpoints.encode)) := by
    have hshape : f8 = .imp query78 (.imp clean19 competitorEndpoints) := by decide
    have h := relabel_point
    rw [hshape] at h
    exact h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [query78.encode,member 10 19,oldClean.encode]
  have hq : Context Γ query78.encode := .head _ _
  have hm : Context Γ (member 10 19) := .hypothesis (by simp [Γ])
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  have hclean : Context Γ clean19.encode := .mp hm (.mp hc (.closed hi))
  exact .mp hclean (.mp hq (.closed hp))

private def innerPair : Formula := pairFormula 18 7 8
private def outerBody : Formula := namedBoth (.member 10 19) (pairFormula 19 18 5)
private def innerBody : Formula := namedBoth innerPair (.ex 19 outerBody)
private theorem old_shape : oldCompetitor = .ex 18 innerBody := by decide
private theorem query_shape : query78 = namedBoth (pairFormula 19 18 5) innerPair := by decide

private def inner_point : KDerivation (imp oldClean.encode
    (imp innerPair.encode (imp outerBody.encode competitorEndpoints.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [outerBody.encode,innerPair.encode,oldClean.encode]
  have ho : Context Γ (both (member 10 19) (pairFormula 19 18 5).encode) := by
    have h : Context Γ outerBody.encode := .head _ _
    simpa [outerBody,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have hi : Context Γ innerPair.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  have hq : Context Γ query78.encode := by
    rw [query_shape]
    simpa [namedBoth,Formula.not,Formula.encode,both,neg] using
      Context.conjunctionIntro (Context.conjunctionRight ho) hi
  exact .mp hq (.mp (Context.conjunctionLeft ho) (.mp hc (.closed point)))

private def inner_exists : KDerivation (imp oldClean.encode
    (imp innerPair.encode (imp (existsCode 19 outerBody.encode) competitorEndpoints.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [existsCode 19 outerBody.encode,innerPair.encode,oldClean.encode]
  have hp : Context [innerPair.encode,oldClean.encode] (imp outerBody.encode competitorEndpoints.encode) :=
    .mp (.head _ _) (.mp (.hypothesis (by simp)) (.closed inner_point))
  have hv : ∀ q, q ∈ [innerPair.encode,oldClean.encode] → KDerivation (imp q (allCode 19 q)) := by
    intro q hq
    by_cases he : q = innerPair.encode
    · subst q; exact innerPair.vacuity 19 (by decide)
    · have he' : q = oldClean.encode := by simpa [he] using hq
      subst q; exact free_vacuity 19 oldClean (by decide)
  have hall := Context.generalize 19 hv hp
  exact Context.existsElim (competitorEndpoints.vacuity 19 (by decide)) (.under hall _) (.head _ _)

/-- Every queried competitor triple in the clean old graph has its major,
minor, and output in the three original product domains. -/
def competitor_endpoints : KDerivation (imp oldClean.encode
    (imp oldCompetitor.encode competitorEndpoints.encode)) := by
  have hpoint : KDerivation (imp oldClean.encode (imp innerBody.encode competitorEndpoints.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [innerBody.encode,oldClean.encode]
    have hb : Context Γ (both innerPair.encode (existsCode 19 outerBody.encode)) := by
      have h : Context Γ innerBody.encode := .head _ _
      simpa [innerBody,namedBoth,Formula.not,Formula.encode,both,neg] using h
    have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
    exact .mp (Context.conjunctionRight hb) (.mp (Context.conjunctionLeft hb) (.mp hc (.closed inner_exists)))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldCompetitor.encode,oldClean.encode]
  have hc : Context [oldClean.encode] oldClean.encode := .head _ _
  have hp : Context [oldClean.encode] (imp innerBody.encode competitorEndpoints.encode) := .mp hc (.closed hpoint)
  have hall := Context.generalize 18 (by
    intro q hq
    have he : q = oldClean.encode := by simpa using hq
    subst q; exact oldClean.vacuity 18 (by decide)) hp
  have he : Context Γ (existsCode 18 innerBody.encode) := by
    have h : Context Γ oldCompetitor.encode := .head _ _
    simpa [old_shape,Formula.encode] using h
  exact Context.existsElim (competitorEndpoints.vacuity 18 (by decide)) (.under hall _) he

theorem competitor_endpoints_certificate : theoremCode (certificate competitor_endpoints) =
    imp oldClean.encode (imp oldCompetitor.encode competitorEndpoints.encode) := certificate_correct competitor_endpoints
end PASoundness.PAtoCompactProductOldCompetitorEndpoints
#print axioms PASoundness.PAtoCompactProductOldCompetitorEndpoints.competitor_endpoints
#print axioms PASoundness.PAtoCompactProductOldCompetitorEndpoints.competitor_endpoints_certificate
