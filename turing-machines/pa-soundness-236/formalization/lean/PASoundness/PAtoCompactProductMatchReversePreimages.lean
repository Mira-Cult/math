import PASoundness.PAtoCompactProductMatchReverseReconstruct
import PASoundness.PAtoCompactTransitiveWitness

/-! Select both source-factor preimages of target-product coordinates under
the two supplied factor-bijection matrices. The selected preimages retain
their directed graph edges and reverse uniqueness clauses. No reverse product
match or global graph property is asserted. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchReversePreimages

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactProductMatchFactorImages PASoundness.PAtoCompactProductMatchReverseProduct
open PASoundness.PAtoCompactProductMatchReverseFactors PASoundness.PAtoCompactProductMatchReverseReconstruct

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def bothPreimages : Formula := namedBoth majorPreimage minorPreimage
def targetRemainder : Formula := namedBoth (PAtoCompactProductMatchTargetOutput.targetTriple 33 34 55)
  (.all 7 (.all 8 (.imp (namedBoth (.member 42 7) (namedBoth (.member 43 8)
    (PAtoCompactProductMatchTargetOutput.targetTriple 7 8 55)))
      (namedBoth (.equal 7 33) (.equal 8 34)))))

theorem target_pair_shape : targetReverseBody = namedBoth (.member 42 33)
    (namedBoth (.member 43 34) targetRemainder) := by decide

/-- A target coordinate pair and both factor-bijection matrices supply both
source preimages, with their original graph and uniqueness clauses. -/
def both_preimages : KDerivation
    (imp targetReverseBody.encode (imp firstBijection.encode (imp secondBijection.encode
      (existsCode 30 (existsCode 31 bothPreimages.encode))))) := by
  let R := targetReverseBody.encode
  let B₁ := firstBijection.encode
  let B₂ := secondBijection.encode
  let F := majorPreimage.encode
  let S := minorPreimage.encode
  let P := bothPreimages.encode
  have hlocal : Context [R,B₁,B₂] (imp F (existsCode 31 P)) := by
    apply Context.deduction
    let Γ := [F,R,B₁,B₂]
    have hf : Context Γ F := .head _ _
    have hr : Context Γ R := .hypothesis (by simp [Γ])
    have hb₂ : Context Γ B₂ := .hypothesis (by simp [Γ])
    have hr' : Context Γ (both (member 42 33) (both (member 43 34) targetRemainder.encode)) := by
      simpa [R, target_pair_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hr
    have hy : Context Γ (member 43 34) := Context.conjunctionLeft (Context.conjunctionRight hr')
    have hs : Context Γ (existsCode 31 S) := .mp hy (.mp hb₂ (.closed minor_preimage))
    have hp : Context Γ (imp S P) := by
      apply Context.deduction
      have hf' : Context (S :: Γ) F := .under hf S
      have hs' : Context (S :: Γ) S := .head _ _
      have h := Context.conjunctionIntro hf' hs'
      simpa [P, F, S, bothPreimages, namedBoth, Formula.not, Formula.encode, both, neg] using h
    have hv : ∀ f, f ∈ Γ → KDerivation (imp f (allCode 31 f)) := by
      intro f h
      simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at h
      by_cases he : f = F
      · subst f; exact majorPreimage.vacuity 31 (by decide)
      · have h' := h.resolve_left he
        by_cases hr : f = R
        · subst f; exact targetReverseBody.vacuity 31 (by decide)
        · have h'' := h'.resolve_left hr
          by_cases hb : f = B₁
          · subst f; exact firstBijection.vacuity 31 (by decide)
          · have hb₂ : f = B₂ := h''.resolve_left hb
            subst f; exact secondBijection.vacuity 31 (by decide)
    exact exists_map_context (Context.generalize 31 hv hp) hs
  have hv : ∀ f, f ∈ [R,B₁,B₂] → KDerivation (imp f (allCode 30 f)) := by
    intro f h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    by_cases he : f = R
    · subst f; exact targetReverseBody.vacuity 30 (by decide)
    · have h' := h.resolve_left he
      by_cases hb : f = B₁
      · subst f; exact firstBijection.vacuity 30 (by decide)
      · have hb₂ : f = B₂ := h'.resolve_left hb
        subst f; exact secondBijection.vacuity 30 (by decide)
  have hall : Context [R,B₁,B₂] (allCode 30 (imp F (existsCode 31 P))) :=
    Context.generalize 30 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [B₂,B₁,R]
  have hb₁ : Context Γ B₁ := .hypothesis (by simp [Γ])
  have hr : Context Γ R := .hypothesis (by simp [Γ])
  have hr' : Context Γ (both (member 42 33) (both (member 43 34) targetRemainder.encode)) := by
    simpa [R, target_pair_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hr
  have hx : Context Γ (member 42 33) := Context.conjunctionLeft hr'
  have hf : Context Γ (existsCode 30 F) := .mp hx (.mp hb₁ (.closed major_preimage))
  have hall' : Context Γ (allCode 30 (imp F (existsCode 31 P))) :=
    Context.weaken hall (by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with h | h | h
      · subst f; simp [Γ]
      · subst f; simp [Γ]
      · subst f; simp [Γ])
  simpa only [P] using (exists_map_context hall' hf)

theorem both_preimages_certificate : theoremCode (certificate both_preimages) =
    imp targetReverseBody.encode (imp firstBijection.encode (imp secondBijection.encode
      (existsCode 30 (existsCode 31 bothPreimages.encode)))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchReversePreimages

#print axioms PASoundness.PAtoCompactProductMatchReversePreimages.both_preimages
#print axioms PASoundness.PAtoCompactProductMatchReversePreimages.both_preimages_certificate
