import PASoundness.PAtoCompactSeededSpanEdgeIntro
import PASoundness.PAtoCompactSeededSpanSeedSourceUnique
import PASoundness.PAtoCompactTransitiveWitness
import PASoundness.PAtoCompactFreeVacuity

/-! Forward coverage on the seed side: the supplied seed bijection produces
an actual seed image, whose cut membership is lifted to the target whole and
whose same edge is introduced into the seeded span. This does not cover the
outside-cut side or assert a complete bijection. -/
namespace PASoundness.PAtoCompactSeededSpanSeedForwardCoverage

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactSeededSpanBase PASoundness.PAtoCompactSeededSpanEdgeIntro
open PASoundness.PAtoCompactSeededSpanSeedSourceUnique

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def cutContained : Formula := .all 5 (.imp (.member 41 5) (.member 8 5))
def seedWitness : Formula := namedBoth (.member 41 3) (namedBoth (graphFormula 14 2 3)
  (.all 4 (.imp (namedBoth (.member 41 4) (graphFormula 14 2 4)) (.equal 4 3))))
def seedForward : Formula := .all 2 (.imp (.member 40 2) (.ex 3 seedWitness))
def outputBody : Formula := namedBoth (.member 8 3) (graphFormula 9 2 3)
def output : Formula := .ex 3 outputBody
def guard : Formula := namedBoth seededSpan (namedBoth seedBijection
  (namedBoth cutContained (namedBoth (.member 0 2) (.member 40 2))))

private def contained_at_three : KDerivation (imp cutContained.encode
    (imp (member 41 3) (member 8 3))) := by
  let body : Formula := .imp (.member 41 5) (.member 8 5)
  have hi := universalInstance 5 3 body (by decide) (by decide) (by decide)
  have ha : replace 5 3 body = .imp (.member 41 3) (.member 8 3) := by decide
  rw [ha] at hi
  simpa only [cutContained,body,Formula.encode] using hi

/-- Under the supplied seed-side guard, the same actual seed image witnesses
an edge of graph9 into the target whole. -/
def seed_forward_coverage : KDerivation (imp guard.encode output.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hi : Context Γ seededSpan.encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hb : Context Γ seedBijection.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hc : Context Γ cutContained.encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hwhole : Context Γ (member 0 2) := Context.conjunctionLeft hr
  have hcut : Context Γ (member 40 2) := Context.conjunctionRight hr
  have hf : Context Γ seedForward.encode := by
    change Context Γ (both seedForward.encode _) at hb
    exact Context.conjunctionLeft hb
  have hforward : Context Γ (imp (member 40 2) (existsCode 3 seedWitness.encode)) := by
    exact .mp hf (.closed (allSpecialize 2 (.imp (.member 40 2) (.ex 3 seedWitness)) (by decide)))
  have hex : Context Γ (existsCode 3 seedWitness.encode) := .mp hcut hforward
  have hlocal : Context Γ (imp seedWitness.encode outputBody.encode) := by
    apply Context.deduction
    let Δ := [seedWitness.encode,guard.encode]
    have hw : Context Δ seedWitness.encode := .head _ _
    have hspan : Context Δ seededSpan.encode := .under hi seedWitness.encode
    have hcontained : Context Δ cutContained.encode := .under hc seedWitness.encode
    have hwhole' : Context Δ (member 0 2) := .under hwhole seedWitness.encode
    have htargetCut : Context Δ (member 41 3) := Context.conjunctionLeft hw
    have hseed : Context Δ (graphFormula 14 2 3).encode :=
      Context.conjunctionLeft (Context.conjunctionRight hw)
    have htarget : Context Δ (member 8 3) := .mp htargetCut (.mp hcontained (.closed contained_at_three))
    have hedge : Context Δ (graphFormula 9 2 3).encode :=
      .mp hseed (.mp (Context.conjunctionIntro hwhole' htarget) (.mp hspan (.closed seed_edge_intro)))
    exact Context.conjunctionIntro htarget hedge
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 3 h)) := by
    intro h hh
    have he : h = guard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 3 guard (by decide)
  have hall := Context.generalize 3 hv hlocal
  simpa only [output,Formula.encode] using exists_map_context hall hex

theorem seed_forward_coverage_certificate : theoremCode (certificate seed_forward_coverage) =
    imp guard.encode output.encode := certificate_correct seed_forward_coverage

end PASoundness.PAtoCompactSeededSpanSeedForwardCoverage

#print axioms PASoundness.PAtoCompactSeededSpanSeedForwardCoverage.cutContained
#print axioms PASoundness.PAtoCompactSeededSpanSeedForwardCoverage.seedWitness
#print axioms PASoundness.PAtoCompactSeededSpanSeedForwardCoverage.seedForward
#print axioms PASoundness.PAtoCompactSeededSpanSeedForwardCoverage.outputBody
#print axioms PASoundness.PAtoCompactSeededSpanSeedForwardCoverage.output
#print axioms PASoundness.PAtoCompactSeededSpanSeedForwardCoverage.guard
#print axioms PASoundness.PAtoCompactSeededSpanSeedForwardCoverage.seed_forward_coverage
#print axioms PASoundness.PAtoCompactSeededSpanSeedForwardCoverage.seed_forward_coverage_certificate
