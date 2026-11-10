import PASoundness.PAtoCompactSeededSpanReverseCoverage
import PASoundness.PAtoCompactConditionalTransitivityReverseClause
import PASoundness.PAtoCompactFreeVacuity

/-! Construct the literal reverse bijection clause from separately supplied
reverse edge coverage and guarded source uniqueness. The same existential
preimage witness is enriched with its K-proved uniqueness property. -/
namespace PASoundness.PAtoCompactReverseBijectionFromCoverage

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactTransitiveWitness PASoundness.PAtoCompactConditionalTransitivitySourceAll
open PASoundness.PAtoCompactConditionalTransitivityReverseClause

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def coverage : Formula := PASoundness.PAtoCompactSeededSpanReverseCoverage.reverseCoverage
private def simpleBody : Formula := PASoundness.PAtoCompactSeededSpanSuffixReverseCoverage.outputBody
def guard : Formula := PASoundness.PAtoCompactZeroSuccessor.namedBoth coverage family

private def family_at_point : KDerivation (imp family.encode
    PASoundness.PAtoCompactConditionalTransitivitySourceAll.point.encode) := by
  have h3 := allSpecialize 3 (.all 2 (.all 4 PASoundness.PAtoCompactConditionalTransitivitySourceAll.point)) (by decide)
  have h2 := allSpecialize 2 (.all 4 PASoundness.PAtoCompactConditionalTransitivitySourceAll.point) (by decide)
  have h4 := allSpecialize 4 PASoundness.PAtoCompactConditionalTransitivitySourceAll.point (by decide)
  simpa only [family,Formula.encode] using compose h3 (compose h2 h4)

/-- Reverse existence plus source uniqueness yield the full second conjunct
of the target bijection; neither premise is inferred here. -/
def reverse_bijection_from_coverage : KDerivation (imp guard.encode rightClause.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hcov : Context Γ coverage.encode := Context.conjunctionLeft hg
  have huniq : Context Γ family.encode := Context.conjunctionRight hg
  have hpoint : Context Γ (imp (member 8 3) (existsCode 2 fullWitness.encode)) := by
    apply Context.deduction
    let Δ := [member 8 3,guard.encode]
    have hm : Context Δ (member 8 3) := .head _ _
    have hcov' : Context Δ coverage.encode := .under hcov (member 8 3)
    have he : Context Δ (existsCode 2 simpleBody.encode) := by
      have hi := allSpecialize 3 PASoundness.PAtoCompactSeededSpanReverseCoverage.point (by decide)
      have hp : Context Δ PASoundness.PAtoCompactSeededSpanReverseCoverage.point.encode := .mp hcov' (.closed hi)
      have hout : Context Δ PASoundness.PAtoCompactSeededSpanReverseCoverage.output.encode := .mp hm hp
      simpa only [PASoundness.PAtoCompactSeededSpanReverseCoverage.output,
        PASoundness.PAtoCompactSeededSpanSuffixReverseCoverage.output,simpleBody,Formula.encode] using hout
    have hlocal : Context Δ (imp simpleBody.encode fullWitness.encode) := by
      apply Context.deduction
      let Θ := [simpleBody.encode,member 8 3,guard.encode]
      have hw : Context Θ simpleBody.encode := .head _ _
      have hm' : Context Θ (member 8 3) := .hypothesis (by simp [Θ])
      have huniq' : Context Θ family.encode := .under (.under huniq (member 8 3)) simpleBody.encode
      have hsource : Context Θ (member 0 2) := Context.conjunctionLeft hw
      have hedge : Context Θ (graphFormula 9 2 3).encode := Context.conjunctionRight hw
      have htest : Context Θ PASoundness.PAtoCompactConditionalTransitivitySourceAll.point.encode :=
        .mp huniq' (.closed family_at_point)
      have hpoint4 : Context Θ candidateBody.encode := by
        apply Context.deduction
        let A := both (member 0 4) (graphFormula 9 4 3).encode
        let Ξ := [A,simpleBody.encode,member 8 3,guard.encode]
        have ha : Context Ξ A := .head _ _
        have hm4 : Context Ξ (member 0 4) := Context.conjunctionLeft ha
        have he4 : Context Ξ (graphFormula 9 4 3).encode := Context.conjunctionRight ha
        have hg4 : Context Ξ PASoundness.PAtoCompactConditionalTransitivitySourceAll.guard.encode :=
          Context.conjunctionIntro (.under hm' A) (Context.conjunctionIntro (.under hsource A)
            (Context.conjunctionIntro hm4 (Context.conjunctionIntro (.under hedge A) he4)))
        exact .mp hg4 (.under htest A)
      have hv4 : ∀ h, h ∈ Θ → KDerivation (imp h (allCode 4 h)) := by
        intro h hh
        simp only [Θ,List.mem_cons,List.not_mem_nil,or_false] at hh
        by_cases he : h = simpleBody.encode
        · subst h; exact free_vacuity 4 simpleBody (by decide)
        · have hr := hh.resolve_left he
          by_cases hm : h = member 8 3
          · subst h; exact free_vacuity 4 (.member 8 3) (by decide)
          · have hg' : h = guard.encode := hr.resolve_left hm
            subst h; exact free_vacuity 4 guard (by decide)
      have hall : Context Θ (allCode 4 candidateBody.encode) := Context.generalize 4 hv4 hpoint4
      exact Context.conjunctionIntro hsource (Context.conjunctionIntro hedge hall)
    have hv2 : ∀ h, h ∈ Δ → KDerivation (imp h (allCode 2 h)) := by
      intro h hh
      simp only [Δ,List.mem_cons,List.not_mem_nil,or_false] at hh
      by_cases he : h = member 8 3
      · subst h; exact free_vacuity 2 (.member 8 3) (by decide)
      · have hg' : h = guard.encode := hh.resolve_left he
        subst h; exact free_vacuity 2 guard (by decide)
    have hall := Context.generalize 2 hv2 hlocal
    exact exists_map_context hall he
  have hv3 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 3 h)) := by
    intro h hh
    have he : h = guard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 3 guard (by decide)
  have hall := Context.generalize 3 hv3 hpoint
  simpa only [rightClause,Formula.encode] using hall

theorem reverse_bijection_from_coverage_certificate : theoremCode (certificate reverse_bijection_from_coverage) =
    imp guard.encode rightClause.encode := certificate_correct reverse_bijection_from_coverage

end PASoundness.PAtoCompactReverseBijectionFromCoverage

#print axioms PASoundness.PAtoCompactReverseBijectionFromCoverage.guard
#print axioms PASoundness.PAtoCompactReverseBijectionFromCoverage.reverse_bijection_from_coverage
#print axioms PASoundness.PAtoCompactReverseBijectionFromCoverage.reverse_bijection_from_coverage_certificate
