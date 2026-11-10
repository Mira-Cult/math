import PASoundness.PAtoCompactSeededSpanCutEquivalenceFromMatrices
import PASoundness.PAtoCompactFreeVacuity

/-! Two supplied isomorphisms from a candidate common source to the cuts
yield the cut-to-cut equivalence, using both actual graph witnesses. -/
namespace PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactPartialCompositionAtSource PASoundness.PAtoCompactConditionalTransitivityMatrix
open PASoundness.PAtoCompactSeededSpanCleanSeedWitness PASoundness.PAtoCompactSeededSpanCutEquivalenceFromMatrices

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def firstBody : Formula := replace 1 40 (replace 0 28 sourceMatrix)
def secondBody : Formula := replace 1 41 (replace 0 28 sourceMatrix)
def firstEquivalence : Formula := .ex 6 firstBody
def secondEquivalence : Formula := .ex 6 secondBody
def guard : Formula := namedBoth (namedCandidate 28) (namedBoth firstEquivalence secondEquivalence)

/-- Capture-safe alpha-renaming gives each existential its own graph label;
the two witnesses are then eliminated without assuming they differ. -/
def cut_equivalence_from_equivalences : KDerivation (imp guard.encode seedEquivalence.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hc : Context Γ (namedCandidate 28).encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have he1 : Context Γ firstEquivalence.encode := Context.conjunctionLeft hr
  have he2 : Context Γ secondEquivalence.encode := Context.conjunctionRight hr
  have ha1 := (existentialAlpha 6 46 firstBody (by decide) (by decide) (by decide)).1
  have ha2 := (existentialAlpha 6 47 secondBody (by decide) (by decide) (by decide)).1
  have h1 : Context Γ (existsCode 46 firstCutMatrix.encode) := by
    simpa only [firstEquivalence, firstCutMatrix, firstBody, Formula.encode] using Context.mp he1 (.closed ha1)
  have h2 : Context Γ (existsCode 47 secondCutMatrix.encode) := by
    simpa only [secondEquivalence, secondCutMatrix, secondBody, Formula.encode] using Context.mp he2 (.closed ha2)
  have hlocal : Context (secondCutMatrix.encode :: firstCutMatrix.encode :: Γ) seedEquivalence.encode := by
    let Δ := [secondCutMatrix.encode,firstCutMatrix.encode,guard.encode]
    have hm2 : Context Δ secondCutMatrix.encode := .head _ _
    have hm1 : Context Δ firstCutMatrix.encode := .hypothesis (by simp [Δ])
    have hc' : Context Δ (namedCandidate 28).encode := by
      exact Context.under (Context.under hc firstCutMatrix.encode) secondCutMatrix.encode
    exact .mp hc' (.mp hm2 (.mp hm1 (.closed cut_equivalence_from_matrices)))
  have hv47 : ∀ h, h ∈ firstCutMatrix.encode :: Γ → KDerivation (imp h (allCode 47 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases he : h = firstCutMatrix.encode
    · subst h; exact free_vacuity 47 firstCutMatrix (by decide)
    · have he' : h = guard.encode := hh.resolve_left he
      subst h; exact free_vacuity 47 guard (by decide)
  have h2' : Context (firstCutMatrix.encode :: Γ) (existsCode 47 secondCutMatrix.encode) :=
    .under h2 _
  have hmid : Context (firstCutMatrix.encode :: Γ) seedEquivalence.encode := Context.existsElim
    (free_vacuity 47 seedEquivalence (by decide)) (Context.generalize 47 hv47 (Context.deduction hlocal)) h2'
  have hv46 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 46 h)) := by
    intro h hh
    have he : h = guard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 46 guard (by decide)
  exact Context.existsElim (free_vacuity 46 seedEquivalence (by decide))
    (Context.generalize 46 hv46 (Context.deduction hmid)) h1

theorem cut_equivalence_from_equivalences_certificate : theoremCode (certificate cut_equivalence_from_equivalences) =
    imp guard.encode seedEquivalence.encode := certificate_correct cut_equivalence_from_equivalences

end PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences

#print axioms PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences.firstBody
#print axioms PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences.secondBody
#print axioms PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences.firstEquivalence
#print axioms PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences.secondEquivalence
#print axioms PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences.guard
#print axioms PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences.cut_equivalence_from_equivalences
#print axioms PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences.cut_equivalence_from_equivalences_certificate
