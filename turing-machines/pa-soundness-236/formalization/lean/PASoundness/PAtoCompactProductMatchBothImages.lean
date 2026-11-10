import PASoundness.PAtoCompactProductMatchPointUnique
import PASoundness.PAtoCompactProductMatchFactorImages
import PASoundness.PAtoCompactTransitiveWitness

/-! Combine the two actual factor-bijection images of coordinates selected
from a product output. The witnesses retain both graph edges and both
uniqueness clauses. This does not yet select the target product output or
collect a represented graph of matched outputs. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchBothImages

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactProductMatchPointWitness PASoundness.PAtoCompactProductMatchPointUnique
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactTransitiveWitness

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def bothImages : Formula := namedBoth firstImage secondImage

/-- From a selected source product coordinate pair and two supplied factor
bijections, select both target coordinates at once. The major image is 33
and the minor image is 34; represented values may coincide. -/
def both_images : KDerivation
    (imp selectedReverseBody.encode (imp firstBijection.encode (imp secondBijection.encode
      (existsCode 33 (existsCode 34 bothImages.encode))))) := by
  let R := selectedReverseBody.encode
  let B₁ := firstBijection.encode
  let B₂ := secondBijection.encode
  let F := firstImage.encode
  let S := secondImage.encode
  let P := bothImages.encode
  have hlocal : Context [R,B₁,B₂] (imp F (existsCode 34 P)) := by
    apply Context.deduction
    let Γ := [F,R,B₁,B₂]
    have hf : Context Γ F := .head _ _
    have hr : Context Γ R := .hypothesis (by simp [Γ])
    have hb₂ : Context Γ B₂ := .hypothesis (by simp [Γ])
    have hr' : Context Γ (both (member 0 30) (both (member 1 31)
        (both (tripleFormula 30 31 32).encode (allCode 7 (allCode 8 reverseUnique.encode))))) := by
      simpa [R, reverse_selected_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hr
    have hy : Context Γ (member 1 31) := Context.conjunctionLeft (Context.conjunctionRight hr')
    have hs : Context Γ (existsCode 34 S) := .mp hy (.mp hb₂ (.closed second_image))
    have hp : Context Γ (imp S P) := by
      apply Context.deduction
      have hf' : Context (S :: Γ) F := .under hf S
      have hs' : Context (S :: Γ) S := .head _ _
      have h := Context.conjunctionIntro hf' hs'
      simpa [P, F, S, bothImages, namedBoth, Formula.not, Formula.encode, both, neg] using h
    have hv : ∀ f, f ∈ Γ → KDerivation (imp f (allCode 34 f)) := by
      intro f h
      simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at h
      by_cases he : f = F
      · subst f; exact firstImage.vacuity 34 (by decide)
      · have h' := h.resolve_left he
        by_cases hr : f = R
        · subst f; exact selectedReverseBody.vacuity 34 (by decide)
        · have h'' := h'.resolve_left hr
          by_cases hb : f = B₁
          · subst f; exact firstBijection.vacuity 34 (by decide)
          · have hb₂ : f = B₂ := h''.resolve_left hb
            subst f; exact secondBijection.vacuity 34 (by decide)
    exact exists_map_context (Context.generalize 34 hv hp) hs
  have hv : ∀ f, f ∈ [R,B₁,B₂] → KDerivation (imp f (allCode 33 f)) := by
    intro f h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    by_cases he : f = R
    · subst f; exact selectedReverseBody.vacuity 33 (by decide)
    · have h' := h.resolve_left he
      by_cases hb : f = B₁
      · subst f; exact firstBijection.vacuity 33 (by decide)
      · have hb₂ : f = B₂ := h'.resolve_left hb
        subst f; exact secondBijection.vacuity 33 (by decide)
  have hall : Context [R,B₁,B₂] (allCode 33 (imp F (existsCode 34 P))) :=
    Context.generalize 33 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [B₂,B₁,R]
  have hb₁ : Context Γ B₁ := .hypothesis (by simp [Γ])
  have hr : Context Γ R := .hypothesis (by simp [Γ])
  have hr' : Context Γ (both (member 0 30) (both (member 1 31)
      (both (tripleFormula 30 31 32).encode (allCode 7 (allCode 8 reverseUnique.encode))))) := by
    simpa [R, reverse_selected_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hr
  have hx : Context Γ (member 0 30) := Context.conjunctionLeft hr'
  have hf : Context Γ (existsCode 33 F) := .mp hx (.mp hb₁ (.closed first_image))
  have hall' : Context Γ (allCode 33 (imp F (existsCode 34 P))) :=
    Context.weaken hall (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with h | h | h
      · subst f; simp [Γ]
      · subst f; simp [Γ]
      · subst f; simp [Γ])
  simpa only [P] using (exists_map_context hall' hf)

theorem both_images_certificate : theoremCode (certificate both_images) =
    imp selectedReverseBody.encode (imp firstBijection.encode (imp secondBijection.encode
      (existsCode 33 (existsCode 34 bothImages.encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchBothImages

#print axioms PASoundness.PAtoCompactProductMatchBothImages.both_images
#print axioms PASoundness.PAtoCompactProductMatchBothImages.both_images_certificate
