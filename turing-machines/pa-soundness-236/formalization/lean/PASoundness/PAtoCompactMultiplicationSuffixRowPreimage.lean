import PASoundness.PAtoCompactMultiplicationSuffixPreimageFive
import PASoundness.PAtoCompactMultiplicationSuffixForwardUnique41
import PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
import PASoundness.PAtoCompactMultiplicationRowCoveragePoint41
import PASoundness.PAtoCompactFreeVacuity

/-! Pointwise suffix coverage by the represented fixed-first row. The map,
its cleanliness, and the row invariant are explicit hypotheses about the
same graph witnesses. This is not product reverse uniqueness, full product
construction, multiplication totality, or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationSuffixRowPreimage
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFixedFirstCoverageBase PASoundness.PAtoCompactFixedFirstPreservedBase
open PASoundness.PAtoCompactMultiplicationSuffixPreimageFive
open PASoundness.PAtoCompactMultiplicationSuffixForwardUnique41 (forward_unique)
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges (suffixClean clean_endpoints)
open PASoundness.PAtoCompactMultiplicationRowCoveragePoint41 (pointWitness coverage_point)
open PASoundness.PAtoCompactFreeVacuity
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The fixed-major row has a represented edge to target 5, with a source
member 41 and its particular pair representative 12. -/
def rowPreimageBody : Formula := namedBoth (.member 31 41)
  (namedBoth (pairFormula 12 30 41) (graphFormula 64 12 5))

def rowPreimageAt41 : Formula := .ex 12 rowPreimageBody

def rowPreimage : Formula := .ex 41 rowPreimageAt41

private def rowFull : Formula := replace 0 31 (rowInvariantPreserved 64)
private def pre : Formula := preimageBody 41
private def W : Formula := pointWitness 11 12

/-- Every member of the suffix has a represented row edge to that same
member. The map-bijection and target-cleanliness predicates refer to graph 6;
the full-prefix row invariant refers to graph 64. No extensional uniqueness
of pair representatives is used. -/
def suffix_row_preimage : KDerivation (imp suffixBijection.encode
    (imp suffixClean.encode (imp rowFull.encode
      (imp (member 40 5) rowPreimage.encode)))) := by
  let B := suffixBijection.encode
  let C := suffixClean.encode
  let R := rowFull.encode
  let M := member 40 5
  let Γ := [M,R,C,B]
  have hm : Context Γ M := .head _ _
  have hr : Context Γ R := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hp : Context Γ (existsCode 41 pre.encode) := by
    exact .mp hm (.mp hb (.closed suffix_preimage))
  have hv41 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 41 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases hM : h = M
    · subst h; exact (Formula.member 40 5).vacuity 41 (by decide)
    by_cases hR : h = R
    · subst h; exact rowFull.vacuity 41 (by decide)
    by_cases hC : h = C
    · subst h; exact suffixClean.vacuity 41 (by decide)
    have hB : h = B := by simpa [hM,hR,hC] using hh
    subst h; exact suffixBijection.vacuity 41 (by decide)
  have hpoint : Context (pre.encode :: Γ) rowPreimageAt41.encode := by
    let Δ := [pre.encode,M,R,C,B]
    have hpre : Context Δ pre.encode := .head _ _
    have hs : Context Δ (member 31 41) := by
      change Context Δ (both (member 31 41) (graphFormula 6 41 5).encode) at hpre
      exact Context.conjunctionLeft hpre
    have hrow' : Context Δ rowFull.encode := .hypothesis (by simp [Δ,R])
    have hrow : Context Δ (existsCode 11 (existsCode 12 W.encode)) :=
      .mp hs (.mp hrow' (.closed coverage_point))
    have hv11 : ∀ h, h ∈ Δ → KDerivation (imp h (allCode 11 h)) := by
      intro h hh
      simp only [Δ,List.mem_cons,List.not_mem_nil,or_false] at hh
      by_cases hP : h = pre.encode
      · subst h; exact pre.vacuity 11 (by decide)
      by_cases hM : h = M
      · subst h; exact (Formula.member 40 5).vacuity 11 (by decide)
      by_cases hR : h = R
      · subst h; exact rowFull.vacuity 11 (by decide)
      by_cases hC : h = C
      · subst h; exact suffixClean.vacuity 11 (by decide)
      have hB : h = B := by simpa [hP,hM,hR,hC] using hh
      subst h; exact suffixBijection.vacuity 11 (by decide)
    have hpoint11 : Context (W.encode :: Δ) rowPreimageAt41.encode := by
      let Θ := [W.encode,pre.encode,M,R,C,B]
      have hw : Context Θ W.encode := .head _ _
      have hparts : Context Θ (both (graphFormula 6 41 11).encode
          (both (pairFormula 12 30 41).encode (graphFormula 64 12 11).encode)) := by
        simpa [W,pointWitness,namedBoth,Formula.encode,Formula.not,both,neg] using hw
      have hf11 := Context.conjunctionLeft hparts
      have hpair := Context.conjunctionLeft (Context.conjunctionRight hparts)
      have hedge := Context.conjunctionRight (Context.conjunctionRight hparts)
      have hpre' : Context Θ (both (member 31 41) (graphFormula 6 41 5).encode) := by
        have h : Context Θ pre.encode := .hypothesis (by simp [Θ])
        simpa [pre,preimageBody,namedBoth,Formula.encode,Formula.not,both,neg] using h
      have hs' := Context.conjunctionLeft hpre'
      have hf5 := Context.conjunctionRight hpre'
      have hm' : Context Θ (member 40 5) := .hypothesis (by simp [Θ,M])
      have hc' : Context Θ suffixClean.encode := .hypothesis (by simp [Θ,C])
      have hb' : Context Θ suffixBijection.encode := .hypothesis (by simp [Θ,B])
      have ht11 : Context Θ (member 40 11) :=
        Context.conjunctionRight (.mp hf11 (.mp hc' (.closed (clean_endpoints 41 11 (by decide)))))
      have heq : Context Θ (equal 5 11) :=
        .mp hf11 (.mp ht11 (.mp hf5 (.mp hm' (.mp hs' (.mp hb' (.closed forward_unique))))))
      have hrep := (equalityReplace 11 5 (graphFormula 64 12 11) (by decide) (by decide)).1
      have hshape : replace 11 5 (graphFormula 64 12 11) = graphFormula 64 12 5 := by decide
      rw [hshape] at hrep
      have hedge5 : Context Θ (graphFormula 64 12 5).encode :=
        .mp hedge (.mp (Context.eqSymm heq) (.closed hrep))
      have hbody : Context Θ rowPreimageBody.encode := by
        simpa [rowPreimageBody,namedBoth,Formula.encode,Formula.not,both,neg] using
          (Context.conjunctionIntro hs' (Context.conjunctionIntro hpair hedge5))
      have hi := existsIntroduce 12 rowPreimageBody (by decide)
      exact .mp hbody (.closed hi)
    have hv12 : ∀ h, h ∈ (W.encode :: Δ).tail → KDerivation (imp h (allCode 12 h)) := by
      intro h hh
      change h ∈ Δ at hh
      simp only [Δ,List.mem_cons,List.not_mem_nil,or_false] at hh
      by_cases hP : h = pre.encode
      · subst h; exact pre.vacuity 12 (by decide)
      by_cases hM : h = M
      · subst h; exact (Formula.member 40 5).vacuity 12 (by decide)
      by_cases hR : h = R
      · subst h; exact rowFull.vacuity 12 (by decide)
      by_cases hC : h = C
      · subst h; exact suffixClean.vacuity 12 (by decide)
      have hB : h = B := by simpa [hP,hM,hR,hC] using hh
      subst h; exact suffixBijection.vacuity 12 (by decide)
    have h12 : Context Δ (imp W.encode rowPreimageAt41.encode) := Context.deduction hpoint11
    have hall12 := Context.generalize 12 hv12 h12
    have hvgoal12 : KDerivation (imp rowPreimageAt41.encode (allCode 12 rowPreimageAt41.encode)) :=
      free_vacuity 12 rowPreimageAt41 (by decide)
    have hinner : Context Δ (imp (existsCode 12 W.encode) rowPreimageAt41.encode) := by
      apply Context.deduction
      exact Context.existsElim hvgoal12 (.under hall12 _) (.head _ _)
    have hall11 := Context.generalize 11 hv11 hinner
    have hvgoal11 : KDerivation (imp rowPreimageAt41.encode (allCode 11 rowPreimageAt41.encode)) :=
      rowPreimageAt41.vacuity 11 (by decide)
    exact Context.existsElim hvgoal11 hall11 hrow
  have hgoal : Context (pre.encode :: Γ) rowPreimage.encode := by
    have hi := existsIntroduce 41 rowPreimageAt41 (by decide)
    exact .mp hpoint (.closed hi)
  have hall := Context.generalize 41 hv41 (Context.deduction hgoal)
  have hvgoal41 : KDerivation (imp rowPreimage.encode (allCode 41 rowPreimage.encode)) :=
    free_vacuity 41 rowPreimage (by decide)
  have hresult : Context Γ rowPreimage.encode := Context.existsElim hvgoal41 hall hp
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hresult

theorem suffix_row_preimage_certificate : theoremCode (certificate suffix_row_preimage) =
    imp suffixBijection.encode (imp suffixClean.encode (imp rowFull.encode
      (imp (member 40 5) rowPreimage.encode))) := certificate_correct suffix_row_preimage
end PASoundness.PAtoCompactMultiplicationSuffixRowPreimage
#print axioms PASoundness.PAtoCompactMultiplicationSuffixRowPreimage.suffix_row_preimage
#print axioms PASoundness.PAtoCompactMultiplicationSuffixRowPreimage.suffix_row_preimage_certificate
