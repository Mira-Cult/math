import PASoundness.PAtoCompactConditionalTransitivityEdgeForward
import PASoundness.PAtoCompactTransitiveWitness

/-! Selected middle and output witnesses for two supplied K bijections.
The same existential witnesses retain their membership, graph-edge, and
uniqueness clauses. No composite graph, uniform choice, or graph collection
is assumed or constructed here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCompositionSelectedImages
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactConditionalTransitivityEdgeForward
open PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The first graph's complete image witness from prefix endpoint 10. -/
def firstImageBody : Formula := namedBoth (.member 1 11)
  (namedBoth (graphFormula 6 10 11)
    (.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 6 10 4)) (.equal 4 11))))

/-- The second graph's complete image witness from the selected middle 11. -/
def secondImageBody : Formula := namedBoth (.member 8 12)
  (namedBoth (graphFormula 7 11 12)
    (.all 4 (.imp (namedBoth (.member 8 4) (graphFormula 7 11 4)) (.equal 4 12))))

def firstTemplate : Formula := namedBoth (.member 1 3)
  (namedBoth (graphFormula 6 2 3)
    (.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 6 2 4)) (.equal 4 3))))
def firstClauseBody : Formula := .imp (.member 0 2) (.ex 3 firstTemplate)

def secondTemplate : Formula := namedBoth (.member 8 3)
  (namedBoth (graphFormula 7 2 3)
    (.all 4 (.imp (namedBoth (.member 8 4) (graphFormula 7 2 4)) (.equal 4 3))))
def secondClauseBody : Formula := .imp (.member 1 2) (.ex 3 secondTemplate)

def selected : Formula := .ex 11 (.ex 12 (namedBoth firstImageBody secondImageBody))

/-- The first bijection chooses an image of source 10, retaining uniqueness. -/
def first_image_exists : KDerivation
    (imp bijectionFormula.encode (imp (member 0 10) (existsCode 11 firstImageBody.encode))) := by
  have hi := universalInstance 2 10 firstClauseBody (by decide) (by decide) (by decide)
  have hs : replace 2 10 firstClauseBody = .imp (.member 0 10)
      (.ex 3 (replace 2 10 firstTemplate)) := by decide
  rw [hs] at hi
  have ha := (existentialAlpha 3 11 (replace 2 10 firstTemplate)
    (by decide) (by decide) (by decide)).1
  have he : replace 3 11 (replace 2 10 firstTemplate) = firstImageBody := by decide
  rw [he] at ha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 0 10,bijectionFormula.encode]
  have hx : Context Γ (member 0 10) := Context.head _ _
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hl : Context Γ (allCode 2 firstClauseBody.encode) := Context.conjunctionLeft hb
  exact .mp (.mp hx (.mp hl (.closed hi))) (.closed ha)

/-- The second bijection chooses an image of the selected middle 11. -/
def second_image_exists : KDerivation
    (imp secondBijection.encode (imp (member 1 11) (existsCode 12 secondImageBody.encode))) := by
  have hi := universalInstance 2 11 secondClauseBody (by decide) (by decide) (by decide)
  have hs : replace 2 11 secondClauseBody = .imp (.member 1 11)
      (.ex 3 (replace 2 11 secondTemplate)) := by decide
  rw [hs] at hi
  have ha := (existentialAlpha 3 12 (replace 2 11 secondTemplate)
    (by decide) (by decide) (by decide)).1
  have he : replace 3 12 (replace 2 11 secondTemplate) = secondImageBody := by decide
  rw [he] at ha
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 11,secondBijection.encode]
  have hx : Context Γ (member 1 11) := Context.head _ _
  have hb : Context Γ secondBijection.encode := .hypothesis (by simp [Γ])
  have hl : Context Γ (allCode 2 secondClauseBody.encode) := Context.conjunctionLeft hb
  exact .mp (.mp hx (.mp hl (.closed hi))) (.closed ha)

/-- Both supplied bijections and source membership construct nested middle and
output witnesses, with both image-uniqueness clauses attached. -/
def selected_images_exist : KDerivation
    (imp bijectionFormula.encode (imp secondBijection.encode
      (imp (member 0 10) selected.encode))) := by
  let F := firstImageBody.encode
  let S := secondImageBody.encode
  let B := secondBijection.encode
  let P := both F S
  have hlocal : Context [B] (imp F (existsCode 12 P)) := by
    apply Context.deduction
    let Γ := [F,B]
    have hf : Context Γ F := Context.head _ _
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have hm : Context Γ (member 1 11) := Context.conjunctionLeft hf
    have hs : Context Γ (existsCode 12 S) := .mp hm (.mp hb (.closed second_image_exists))
    have hc : Context Γ (imp S P) := by
      apply Context.deduction
      exact Context.conjunctionIntro (Context.under hf S) (Context.head Γ S)
    have hv : ∀ f, f ∈ Γ → KDerivation (imp f (allCode 12 f)) := by
      intro f hmem
      simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hmem
      by_cases h : f = F
      · subst f; exact firstImageBody.vacuity 12 (by decide)
      · have he : f = B := hmem.resolve_left h
        subst f
        exact secondBijection.vacuity 12 (by decide)
    exact exists_map_context (Context.generalize 12 hv hc) hs
  have hv : ∀ f, f ∈ [B] → KDerivation (imp f (allCode 11 f)) := by
    intro f hf
    have he : f = B := by simpa using hf
    subst f
    exact secondBijection.vacuity 11 (by decide)
  have hall : Context [B] (allCode 11 (imp F (existsCode 12 P))) := Context.generalize 11 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 0 10,B,bijectionFormula.encode]
  have hx : Context Γ (member 0 10) := Context.head _ _
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hf : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have hfirst : Context Γ (existsCode 11 F) := .mp hx (.mp hf (.closed first_image_exists))
  have hall' : Context Γ (allCode 11 (imp F (existsCode 12 P))) :=
    Context.weaken hall (by intro a ha; simp only [List.mem_singleton] at ha; subst a; simp [Γ])
  exact exists_map_context hall' hfirst

theorem selected_images_exist_certificate : theoremCode (certificate selected_images_exist) =
    imp bijectionFormula.encode (imp secondBijection.encode (imp (member 0 10) selected.encode)) :=
  certificate_correct selected_images_exist

end PASoundness.PAtoCompactCompositionSelectedImages

#print axioms PASoundness.PAtoCompactCompositionSelectedImages.selected_images_exist
#print axioms PASoundness.PAtoCompactCompositionSelectedImages.selected_images_exist_certificate
