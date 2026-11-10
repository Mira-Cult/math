import PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha
import PASoundness.PAtoCompactFreeVacuity

/-! A generic finite K lift from a supplied pointwise competitor proof to a
full nested product-triple proof. The graph and pair witnesses remain the
same objects through the lift. The pointwise implication is explicit proof
data; this does not construct the graph, establish its cases, or prove
multiplication totality. No uniqueness of pair representatives is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCompetitorTripleLift
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha
open PASoundness.PAtoCompactFreeVacuity
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Same-edge pair descriptions for queried coordinates (7,8,5). -/
def competitorPairs : Formula := namedBoth (pairFormula 63 18 5) (pairFormula 18 7 8)
/-- The competitor's required coordinates. -/
def competitorEqualities : Formula := namedBoth (.equal 7 30) (.equal 8 41)
/-- The actual queried triple on extended graph 64. -/
def competitorTriple : Formula := replace 4 8 (replace 3 7 queriedTriple)
/-- The relabeled query is exactly the multiplication triple at graph 64. -/
theorem competitorTriple_shape : competitorTriple =
    replace 6 64 (PASoundness.PAtoCompactMultiplicationCandidate.tripleFormula 7 8 5) := by decide
private def expandedCompetitor : Formula := replace 4 8 (replace 3 7 expandedTriple)
private def innerPair : Formula := pairFormula 18 7 8
private def outer : Formula := namedBoth (.member 64 63) (pairFormula 63 18 5)
private def body : Formula := namedBoth innerPair outer

private def original : Formula := .imp queriedTriple expandedTriple
private def at7 : Formula := replace 3 7 original
private def at8 : Formula := replace 4 8 at7
private def expand : KDerivation (imp competitorTriple.encode expandedCompetitor.encode) := by
  have h0 : KDerivation original.encode := triple_to_expanded
  have h1 : KDerivation at7.encode := .mp (.generalize 3 h0)
    (universalInstance 3 7 original (by decide) (by decide) (by decide))
  have h2 : KDerivation at8.encode := .mp (.generalize 4 h1)
    (universalInstance 4 8 at7 (by decide) (by decide) (by decide))
  have hs : at8 = .imp competitorTriple expandedCompetitor := by decide
  rw [hs] at h2
  exact h2

private def lift_exists (x P A B : Nat)
    (hP : KDerivation (imp P (allCode x P)))
    (hB : KDerivation (imp B (allCode x B)))
    (h : KDerivation (imp P (imp A B))) : KDerivation (imp P (imp (existsCode x A) B)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have hp : Context [P] P := .head _ _
  have hs : Context [P] (imp A B) := .mp hp (.closed h)
  have hv : ∀ z, z ∈ [P] → KDerivation (imp z (allCode x z)) := by
    intro z hz
    have he : z = P := by simpa using hz
    subst z
    exact hP
  have hall : Context [P] (allCode x (imp A B)) := Context.generalize x hv hs
  exact Context.existsElim hB (.under hall _) (.head _ _)

/-- A pointwise same-edge competitor proof under H lifts through both
actual existential witnesses in the queried triple. The pointwise K proof
remains an explicit input and H must avoid the witness names. -/
def competitor_of_point (H : Formula) (h18 : 18 ∉ H.names) (h63 : 63 ∉ H.names)
    (point : KDerivation (imp H.encode (imp competitorPairs.encode
      (imp (member 64 63) competitorEqualities.encode)))) :
    KDerivation (imp H.encode (imp competitorTriple.encode competitorEqualities.encode)) := by
  have hlocal : KDerivation (imp H.encode (imp body.encode competitorEqualities.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [body.encode,H.encode]
    have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
    have hb : Context Γ (both innerPair.encode
        (both (member 64 63) (pairFormula 63 18 5).encode)) := by
      have h : Context Γ body.encode := .head _ _
      simpa [body,outer,namedBoth,Formula.not,Formula.encode,both,neg] using h
    have hq : Context Γ competitorPairs.encode := by
      have h := Context.conjunctionIntro (Context.conjunctionRight (Context.conjunctionRight hb))
        (Context.conjunctionLeft hb)
      simpa [competitorPairs,innerPair,namedBoth,Formula.not,Formula.encode,both,neg] using h
    exact .mp (Context.conjunctionLeft (Context.conjunctionRight hb))
      (.mp hq (.mp hh (.closed point)))
  have h63' := lift_exists 63 H.encode body.encode competitorEqualities.encode
    (H.vacuity 63 h63) (competitorEqualities.vacuity 63 (by decide)) hlocal
  have h18' := lift_exists 18 H.encode (existsCode 63 body.encode) competitorEqualities.encode
    (H.vacuity 18 h18) (competitorEqualities.vacuity 18 (by decide)) h63'
  have hshape : expandedCompetitor = .ex 18 (.ex 63 body) := by decide
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [competitorTriple.encode,H.encode]
  have ht : Context Γ competitorTriple.encode := .head _ _
  have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
  have he : Context Γ (existsCode 18 (existsCode 63 body.encode)) := by
    have he := Context.mp ht (.closed expand)
    simpa [hshape,Formula.encode] using he
  exact .mp he (.mp hh (.closed h18'))

theorem competitor_of_point_certificate (H : Formula) (h18 : 18 ∉ H.names) (h63 : 63 ∉ H.names)
    (point : KDerivation (imp H.encode (imp competitorPairs.encode
      (imp (member 64 63) competitorEqualities.encode)))) :
    theoremCode (certificate (competitor_of_point H h18 h63 point)) =
      imp H.encode (imp competitorTriple.encode competitorEqualities.encode) :=
  certificate_correct (competitor_of_point H h18 h63 point)
end PASoundness.PAtoCompactMultiplicationCompetitorTripleLift
#print axioms PASoundness.PAtoCompactMultiplicationCompetitorTripleLift.competitor_of_point
#print axioms PASoundness.PAtoCompactMultiplicationCompetitorTripleLift.competitor_of_point_certificate
