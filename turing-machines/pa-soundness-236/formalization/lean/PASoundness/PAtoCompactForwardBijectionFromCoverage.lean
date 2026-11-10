import PASoundness.PAtoCompactSeededSpanForwardCoverage
import PASoundness.PAtoCompactConditionalTransitivityForwardClause
import PASoundness.PAtoCompactFreeVacuity

/-! Construct the literal forward bijection clause from separately supplied
forward edge coverage and guarded target uniqueness. The same existential
image witness is enriched with its K-proved uniqueness property. -/
namespace PASoundness.PAtoCompactForwardBijectionFromCoverage

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactTransitiveWitness PASoundness.PAtoCompactConditionalTransitivityTargetAll
open PASoundness.PAtoCompactConditionalTransitivityForwardClause

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def coverage : Formula := PASoundness.PAtoCompactSeededSpanForwardCoverage.forwardCoverage
private def simpleBody : Formula := PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage.outputBody
def guard : Formula := PASoundness.PAtoCompactZeroSuccessor.namedBoth coverage targetFamily
private def at4 : Formula := .imp (.member 0 2) (.imp (.member 8 3) (.imp (.member 8 4)
  (.imp (graphFormula 9 2 3) (.imp (graphFormula 9 2 4) (.equal 4 3)))))

private def target_at4 : KDerivation (imp targetFamily.encode at4.encode) := by
  have h2 := allSpecialize 2 (.all 3 (.all 5 targetBody)) (by decide)
  have h3 := allSpecialize 3 (.all 5 targetBody) (by decide)
  have h5 := universalInstance 5 4 targetBody (by decide) (by decide) (by decide)
  have ha : replace 5 4 targetBody = at4 := by decide
  rw [ha] at h5
  simpa only [targetFamily,Formula.encode] using compose h2 (compose h3 h5)

/-- Forward existence plus target uniqueness yield the full first conjunct of
the target bijection; neither premise is inferred here. -/
def forward_bijection_from_coverage : KDerivation (imp guard.encode forwardClause.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hcov : Context Γ coverage.encode := Context.conjunctionLeft hg
  have huniq : Context Γ targetFamily.encode := Context.conjunctionRight hg
  have hpoint : Context Γ (imp (member 0 2) selected.encode) := by
    apply Context.deduction
    let Δ := [member 0 2,guard.encode]
    have hm : Context Δ (member 0 2) := .head _ _
    have hcov' : Context Δ coverage.encode := .under hcov (member 0 2)
    have he : Context Δ (existsCode 3 simpleBody.encode) := by
      have hi := allSpecialize 2 PASoundness.PAtoCompactSeededSpanForwardCoverage.point (by decide)
      have hp : Context Δ PASoundness.PAtoCompactSeededSpanForwardCoverage.point.encode := .mp hcov' (.closed hi)
      have hout : Context Δ PASoundness.PAtoCompactSeededSpanForwardCoverage.output.encode := .mp hm hp
      simpa only [PASoundness.PAtoCompactSeededSpanForwardCoverage.output,
        PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage.output,simpleBody,Formula.encode] using hout
    have hlocal : Context Δ (imp simpleBody.encode witnessBody.encode) := by
      apply Context.deduction
      let Θ := [simpleBody.encode,member 0 2,guard.encode]
      have hw : Context Θ simpleBody.encode := .head _ _
      have hm' : Context Θ (member 0 2) := .hypothesis (by simp [Θ])
      have huniq' : Context Θ targetFamily.encode := .under (.under huniq (member 0 2)) simpleBody.encode
      have htarget : Context Θ (member 8 3) := Context.conjunctionLeft hw
      have hedge : Context Θ (graphFormula 9 2 3).encode := Context.conjunctionRight hw
      have htest : Context Θ at4.encode := .mp huniq' (.closed target_at4)
      have hpoint4 : Context Θ uniqueBody.encode := by
        apply Context.deduction
        let A := both (member 8 4) (graphFormula 9 2 4).encode
        let Ξ := [A,simpleBody.encode,member 0 2,guard.encode]
        have ha : Context Ξ A := .head _ _
        have hm4 : Context Ξ (member 8 4) := Context.conjunctionLeft ha
        have he4 : Context Ξ (graphFormula 9 2 4).encode := Context.conjunctionRight ha
        exact .mp he4 (.mp (.under hedge A) (.mp hm4 (.mp (.under htarget A)
          (.mp (.under hm' A) (.under htest A)))))
      have hv4 : ∀ h, h ∈ Θ → KDerivation (imp h (allCode 4 h)) := by
        intro h hh
        simp only [Θ,List.mem_cons,List.not_mem_nil,or_false] at hh
        by_cases he : h = simpleBody.encode
        · subst h; exact free_vacuity 4 simpleBody (by decide)
        · have hr := hh.resolve_left he
          by_cases hm : h = member 0 2
          · subst h; exact free_vacuity 4 (.member 0 2) (by decide)
          · have hg' : h = guard.encode := hr.resolve_left hm
            subst h; exact free_vacuity 4 guard (by decide)
      have hall : Context Θ (allCode 4 uniqueBody.encode) := Context.generalize 4 hv4 hpoint4
      exact Context.conjunctionIntro htarget (Context.conjunctionIntro hedge hall)
    have hv3 : ∀ h, h ∈ Δ → KDerivation (imp h (allCode 3 h)) := by
      intro h hh
      simp only [Δ,List.mem_cons,List.not_mem_nil,or_false] at hh
      by_cases he : h = member 0 2
      · subst h; exact free_vacuity 3 (.member 0 2) (by decide)
      · have hg' : h = guard.encode := hh.resolve_left he
        subst h; exact free_vacuity 3 guard (by decide)
    have hall := Context.generalize 3 hv3 hlocal
    simpa only [selected,Formula.encode] using exists_map_context hall he
  have hv2 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    have he : h = guard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 2 guard (by decide)
  have hall := Context.generalize 2 hv2 hpoint
  simpa only [forwardClause,Formula.encode] using hall

theorem forward_bijection_from_coverage_certificate : theoremCode (certificate forward_bijection_from_coverage) =
    imp guard.encode forwardClause.encode := certificate_correct forward_bijection_from_coverage

end PASoundness.PAtoCompactForwardBijectionFromCoverage

#print axioms PASoundness.PAtoCompactForwardBijectionFromCoverage.guard
#print axioms PASoundness.PAtoCompactForwardBijectionFromCoverage.forward_bijection_from_coverage
#print axioms PASoundness.PAtoCompactForwardBijectionFromCoverage.forward_bijection_from_coverage_certificate
