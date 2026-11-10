import PASoundness.PAtoCompactSeededSpanSeedForwardCoverage

/-! Reverse coverage on the seed side: the supplied seed bijection produces
an actual seed preimage, whose cut membership is lifted to the source whole
and whose same edge is introduced into the seeded span. This does not cover
outside-cut targets or assert a complete bijection. -/
namespace PASoundness.PAtoCompactSeededSpanSeedReverseCoverage

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactSeededSpanBase PASoundness.PAtoCompactSeededSpanEdgeIntro
open PASoundness.PAtoCompactSeededSpanSeedSourceUnique

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def cutContained : Formula := .all 5 (.imp (.member 40 5) (.member 0 5))
def seedWitness : Formula := namedBoth (.member 40 2) (namedBoth (graphFormula 14 2 3)
  (.all 4 (.imp (namedBoth (.member 40 4) (graphFormula 14 4 3)) (.equal 4 2))))
def seedReverse : Formula := .all 3 (.imp (.member 41 3) (.ex 2 seedWitness))
def outputBody : Formula := namedBoth (.member 0 2) (graphFormula 9 2 3)
def output : Formula := .ex 2 outputBody
def guard : Formula := namedBoth seededSpan (namedBoth seedBijection
  (namedBoth cutContained (namedBoth (.member 8 3) (.member 41 3))))

private def contained_at_two : KDerivation (imp cutContained.encode
    (imp (member 40 2) (member 0 2))) := by
  let body : Formula := .imp (.member 40 5) (.member 0 5)
  have hi := universalInstance 5 2 body (by decide) (by decide) (by decide)
  have ha : replace 5 2 body = .imp (.member 40 2) (.member 0 2) := by decide
  rw [ha] at hi
  simpa only [cutContained,body,Formula.encode] using hi

/-- Under the supplied seed-side guard, the same actual seed preimage
witnesses an edge of graph9 from the source whole. -/
def seed_reverse_coverage : KDerivation (imp guard.encode output.encode) := by
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
  have hwhole : Context Γ (member 8 3) := Context.conjunctionLeft hr
  have hcut : Context Γ (member 41 3) := Context.conjunctionRight hr
  have hf : Context Γ seedReverse.encode := by
    change Context Γ (both _ seedReverse.encode) at hb
    exact Context.conjunctionRight hb
  have hreverse : Context Γ (imp (member 41 3) (existsCode 2 seedWitness.encode)) := by
    exact .mp hf (.closed (allSpecialize 3 (.imp (.member 41 3) (.ex 2 seedWitness)) (by decide)))
  have hex : Context Γ (existsCode 2 seedWitness.encode) := .mp hcut hreverse
  have hlocal : Context Γ (imp seedWitness.encode outputBody.encode) := by
    apply Context.deduction
    let Δ := [seedWitness.encode,guard.encode]
    have hw : Context Δ seedWitness.encode := .head _ _
    have hspan : Context Δ seededSpan.encode := .under hi seedWitness.encode
    have hcontained : Context Δ cutContained.encode := .under hc seedWitness.encode
    have hwhole' : Context Δ (member 8 3) := .under hwhole seedWitness.encode
    have hsourceCut : Context Δ (member 40 2) := Context.conjunctionLeft hw
    have hseed : Context Δ (graphFormula 14 2 3).encode :=
      Context.conjunctionLeft (Context.conjunctionRight hw)
    have hsource : Context Δ (member 0 2) := .mp hsourceCut (.mp hcontained (.closed contained_at_two))
    have hedge : Context Δ (graphFormula 9 2 3).encode :=
      .mp hseed (.mp (Context.conjunctionIntro hsource hwhole') (.mp hspan (.closed seed_edge_intro)))
    exact Context.conjunctionIntro hsource hedge
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    have he : h = guard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 2 guard (by decide)
  have hall := Context.generalize 2 hv hlocal
  simpa only [output,Formula.encode] using exists_map_context hall hex

theorem seed_reverse_coverage_certificate : theoremCode (certificate seed_reverse_coverage) =
    imp guard.encode output.encode := certificate_correct seed_reverse_coverage

end PASoundness.PAtoCompactSeededSpanSeedReverseCoverage

#print axioms PASoundness.PAtoCompactSeededSpanSeedReverseCoverage.cutContained
#print axioms PASoundness.PAtoCompactSeededSpanSeedReverseCoverage.seedWitness
#print axioms PASoundness.PAtoCompactSeededSpanSeedReverseCoverage.seedReverse
#print axioms PASoundness.PAtoCompactSeededSpanSeedReverseCoverage.outputBody
#print axioms PASoundness.PAtoCompactSeededSpanSeedReverseCoverage.output
#print axioms PASoundness.PAtoCompactSeededSpanSeedReverseCoverage.guard
#print axioms PASoundness.PAtoCompactSeededSpanSeedReverseCoverage.seed_reverse_coverage
#print axioms PASoundness.PAtoCompactSeededSpanSeedReverseCoverage.seed_reverse_coverage_certificate
